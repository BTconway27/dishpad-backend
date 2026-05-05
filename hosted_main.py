"""
Dishpad Hosted Backend
======================
Deployed on Render.com. Handles:
  - Recipe clipping (/api/clip) and photo scanning (/api/scan) — uses YOUR Anthropic API key
  - Stripe payments + Pro activation/check
  - Stripe webhook backup
  - Admin dashboard API

Environment variables (set on Render):
  ANTHROPIC_API_KEY        — your Anthropic key (required for AI features)
  STRIPE_SECRET_KEY        — from Stripe dashboard
  STRIPE_WEBHOOK_SECRET    — from Stripe webhook settings
  SMTP_HOST                — e.g. smtp.mail.me.com or smtp.gmail.com
  SMTP_PORT                — 587 (TLS) or 465 (SSL)
  SMTP_USER                — your email address
  SMTP_PASSWORD            — app-specific password
  ADMIN_PASSWORD           — password for admin dashboard
  DISHPAD_PRICE_CENTS      — default 800 ($8)
  FREE_CLIPS_PER_DAY       — default 5 (free tier daily limit per IP)
  DB_PATH                  — path to SQLite DB (default /data/dishpad.db for Render)
"""

import os
import re
import ssl
import csv
import io
import json
import time
import uuid
import hashlib
import asyncio
import secrets
import sqlite3
import smtplib
from datetime import datetime, timezone
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from functools import partial
from typing import Optional

import anthropic
import httpx
import stripe
from fastapi import FastAPI, Request, HTTPException, Header
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse
from pydantic import BaseModel
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded
from recipe_scrapers import scrape_html
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------------
# App setup
# ---------------------------------------------------------------------------

limiter = Limiter(key_func=get_remote_address)
app = FastAPI(title="Dishpad Hosted API")
app.state.limiter = limiter
app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

stripe.api_key    = os.environ.get("STRIPE_SECRET_KEY", "")
WEBHOOK_SECRET    = os.environ.get("STRIPE_WEBHOOK_SECRET", "")
ADMIN_PASSWORD    = os.environ.get("ADMIN_PASSWORD", "changeme")
PRICE_CENTS       = int(os.environ.get("DISHPAD_PRICE_CENTS", "800"))
FREE_CLIPS_PER_DAY = int(os.environ.get("FREE_CLIPS_PER_DAY", "5"))
YOUTUBE_API_KEY   = os.environ.get("YOUTUBE_API_KEY", "")

SMTP_HOST     = os.environ.get("SMTP_HOST", "")
SMTP_PORT     = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER     = os.environ.get("SMTP_USER", "")
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "")

DB_PATH = os.environ.get("DB_PATH", os.path.join(os.path.dirname(__file__), "dishpad_hosted.db"))

# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------

def get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)
    conn = get_db()
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS purchases (
            id                    INTEGER PRIMARY KEY AUTOINCREMENT,
            license_key           TEXT    NOT NULL UNIQUE,
            email                 TEXT    NOT NULL COLLATE NOCASE,
            name                  TEXT,
            stripe_payment_intent TEXT    NOT NULL UNIQUE,
            amount_cents          INTEGER NOT NULL DEFAULT 800,
            created_at            INTEGER NOT NULL,
            is_revoked            INTEGER NOT NULL DEFAULT 0
        );
        CREATE INDEX IF NOT EXISTS idx_purchases_email ON purchases(email);

        CREATE TABLE IF NOT EXISTS clip_usage (
            ip    TEXT    NOT NULL PRIMARY KEY,
            count INTEGER NOT NULL DEFAULT 0
        );

        CREATE TABLE IF NOT EXISTS accounts (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            email         TEXT    NOT NULL UNIQUE COLLATE NOCASE,
            password_hash TEXT    NOT NULL,
            password_salt TEXT    NOT NULL,
            created_at    INTEGER NOT NULL
        );

        CREATE TABLE IF NOT EXISTS auth_sessions (
            token      TEXT    NOT NULL PRIMARY KEY,
            email      TEXT    NOT NULL COLLATE NOCASE,
            created_at INTEGER NOT NULL,
            expires_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_sessions_email ON auth_sessions(email);
    """)
    conn.commit()
    conn.close()


init_db()

# ---------------------------------------------------------------------------
# Helpers — password + session auth
# ---------------------------------------------------------------------------

def _hash_password(password: str, salt: str) -> str:
    return hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 260_000).hex()

def _create_session(email: str) -> str:
    token = secrets.token_hex(32)
    now = int(time.time())
    expires = now + 30 * 24 * 60 * 60  # 30 days
    conn = get_db()
    conn.execute(
        "INSERT INTO auth_sessions (token, email, created_at, expires_at) VALUES (?, ?, ?, ?)",
        (token, email.lower(), now, expires),
    )
    conn.commit()
    conn.close()
    return token

def _get_session_email(token: str) -> Optional[str]:
    if not token:
        return None
    conn = get_db()
    row = conn.execute(
        "SELECT email FROM auth_sessions WHERE token = ? AND expires_at > ?",
        (token, int(time.time())),
    ).fetchone()
    conn.close()
    return row[0] if row else None

# ---------------------------------------------------------------------------
# Helpers — admin auth
# ---------------------------------------------------------------------------

def require_admin(password: Optional[str]) -> None:
    if not ADMIN_PASSWORD or password != ADMIN_PASSWORD:
        raise HTTPException(status_code=401, detail="Invalid admin password")

# ---------------------------------------------------------------------------
# Helpers — pro status & rate limiting
# ---------------------------------------------------------------------------

def is_email_pro(email: str) -> bool:
    if not email:
        return False
    conn = get_db()
    row = conn.execute(
        "SELECT id FROM purchases WHERE email = ? AND is_revoked = 0 LIMIT 1",
        (email.strip().lower(),),
    ).fetchone()
    conn.close()
    return row is not None


def check_and_increment_free_usage(ip: str) -> bool:
    """Return True if under lifetime free clip limit, and increment. Return False if exceeded."""
    conn = get_db()
    row = conn.execute("SELECT count FROM clip_usage WHERE ip = ?", (ip,)).fetchone()
    count = row["count"] if row else 0
    if count >= FREE_CLIPS_PER_DAY:
        conn.close()
        return False
    if row:
        conn.execute("UPDATE clip_usage SET count = count + 1 WHERE ip = ?", (ip,))
    else:
        conn.execute("INSERT INTO clip_usage (ip, count) VALUES (?, 1)", (ip,))
    conn.commit()
    conn.close()
    return True


def get_client_ip(request: Request) -> str:
    forwarded = request.headers.get("X-Forwarded-For")
    if forwarded:
        return forwarded.split(",")[0].strip()
    return request.client.host if request.client else "unknown"

# ---------------------------------------------------------------------------
# Email (SMTP)
# ---------------------------------------------------------------------------

def _smtp_send(to: str, subject: str, html_body: str) -> bool:
    if not SMTP_HOST or not SMTP_USER or not SMTP_PASSWORD:
        print("[Dishpad] SMTP not configured — skipping email")
        return False
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"]    = f"Dishpad <{SMTP_USER}>"
    msg["To"]      = to
    msg["Reply-To"] = SMTP_USER
    msg.attach(MIMEText(html_body, "html", "utf-8"))
    try:
        context = ssl.create_default_context()
        if SMTP_PORT == 465:
            with smtplib.SMTP_SSL(SMTP_HOST, 465, context=context) as server:
                server.login(SMTP_USER, SMTP_PASSWORD)
                server.sendmail(SMTP_USER, to, msg.as_string())
        else:
            with smtplib.SMTP(SMTP_HOST, SMTP_PORT) as server:
                server.starttls(context=context)
                server.login(SMTP_USER, SMTP_PASSWORD)
                server.sendmail(SMTP_USER, to, msg.as_string())
        return True
    except Exception as e:
        print(f"[Dishpad] Email failed: {e}")
        return False


def _email_wrapper(content_html: str) -> str:
    return f"""<!DOCTYPE html>
<html>
<body style="margin:0;padding:0;background:#F9F6F3;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;">
  <table width="100%" cellpadding="0" cellspacing="0" style="background:#F9F6F3;padding:40px 0;">
    <tr><td align="center">
      <table width="520" cellpadding="0" cellspacing="0" style="background:#FFFFFF;border-radius:16px;overflow:hidden;box-shadow:0 2px 12px rgba(0,0,0,0.08);">
        <tr><td style="background:#C0714F;padding:28px 40px;text-align:center;">
          <h1 style="margin:0;color:#FFFFFF;font-size:22px;font-weight:700;">Dishpad</h1>
        </td></tr>
        <tr><td style="padding:36px 40px;font-size:15px;color:#374151;line-height:1.7;">
          {content_html}
        </td></tr>
        <tr><td style="background:#FAF7F4;padding:20px 40px;border-top:1px solid #EDE8E3;">
          <p style="margin:0;font-size:12px;color:#9CA3AF;">Questions? Reply to this email. &nbsp;© 2026 Dishpad.</p>
        </td></tr>
      </table>
    </td></tr>
  </table>
</body>
</html>"""


def send_receipt_email(email: str, name: str) -> None:
    first = (name or "there").split()[0]
    content = f"""
<h2 style="margin:0 0 8px;font-size:20px;color:#2D2A27;">You're all set, {first}!</h2>
<p style="margin:0 0 24px;color:#6B7280;">Your Dishpad Pro purchase is confirmed. Unlimited recipes, forever — no subscription needed.</p>
<div style="background:#FAF7F4;border:1.5px solid #E8DDD6;border-radius:12px;padding:20px;text-align:center;margin-bottom:24px;">
  <p style="margin:0 0 4px;font-size:11px;color:#9CA3AF;text-transform:uppercase;letter-spacing:0.08em;font-weight:600;">Registered to</p>
  <p style="margin:0;font-size:18px;font-weight:700;color:#C0714F;">{email}</p>
</div>
<p style="margin:0;color:#374151;">To restore Pro on any device, open Dishpad → Settings → Restore Purchase and enter this email address.</p>"""
    _smtp_send(email, "Welcome to Dishpad Pro", _email_wrapper(content))


def send_bulk_email(emails: list, subject: str, body_html: str) -> int:
    if not SMTP_HOST or not SMTP_USER or not SMTP_PASSWORD:
        print("[Dishpad] SMTP not configured — skipping bulk email")
        return 0
    wrapped = _email_wrapper(body_html.replace("\n", "<br>"))
    sent = 0
    try:
        context = ssl.create_default_context()
        smtp_cls = smtplib.SMTP_SSL(SMTP_HOST, 465, context=context) if SMTP_PORT == 465 else smtplib.SMTP(SMTP_HOST, SMTP_PORT)
        with smtp_cls as server:
            if SMTP_PORT != 465:
                server.starttls(context=context)
            server.login(SMTP_USER, SMTP_PASSWORD)
            for addr in emails:
                try:
                    msg = MIMEMultipart("alternative")
                    msg["Subject"] = subject
                    msg["From"]    = f"Dishpad <{SMTP_USER}>"
                    msg["To"]      = addr
                    msg["Reply-To"] = SMTP_USER
                    msg.attach(MIMEText(wrapped, "html", "utf-8"))
                    server.sendmail(SMTP_USER, addr, msg.as_string())
                    sent += 1
                except Exception as e:
                    print(f"[Dishpad] Failed to send to {addr}: {e}")
    except Exception as e:
        print(f"[Dishpad] SMTP connection failed: {e}")
    return sent

# ---------------------------------------------------------------------------
# Pydantic models
# ---------------------------------------------------------------------------

class ClipRequest(BaseModel):
    url: str
    proEmail: Optional[str] = None


class ScanRequest(BaseModel):
    image: str
    mediaType: str = "image/jpeg"
    proEmail: Optional[str] = None


class CreateIntentRequest(BaseModel):
    email: str
    name: str = ""


class ActivateProRequest(BaseModel):
    payment_intent_id: str
    email: str
    name: str = ""


class CheckProRequest(BaseModel):
    email: str


class ValidateLicenseRequest(BaseModel):
    license_key: str


class RevokeRequest(BaseModel):
    licenseKey: str  # camelCase matches frontend


class EmailRequest(BaseModel):
    email: str


class SendUpdateRequest(BaseModel):
    subject: str
    body: str

class AuthRegisterRequest(BaseModel):
    email: str
    password: str

class AuthLoginRequest(BaseModel):
    email: str
    password: str

class AuthSessionRequest(BaseModel):
    token: str

# ---------------------------------------------------------------------------
# Health
# ---------------------------------------------------------------------------

@app.get("/")
async def root():
    return {"status": "ok"}

@app.get("/health")
async def health():
    return {"status": "ok", "email_configured": bool(SMTP_HOST and SMTP_USER)}

# ---------------------------------------------------------------------------
# Auth endpoints
# ---------------------------------------------------------------------------

@app.post("/api/auth/register")
@limiter.limit("5/minute")
async def auth_register(request: Request, body: AuthRegisterRequest):
    email = body.email.strip().lower()
    password = body.password
    if not email or "@" not in email:
        raise HTTPException(status_code=400, detail="Valid email is required")
    if len(password) < 8:
        raise HTTPException(status_code=400, detail="Password must be at least 8 characters")
    conn = get_db()
    existing = conn.execute("SELECT id FROM accounts WHERE email = ?", (email,)).fetchone()
    if existing:
        conn.close()
        raise HTTPException(status_code=409, detail="An account with that email already exists")
    salt = secrets.token_hex(16)
    pw_hash = _hash_password(password, salt)
    conn.execute(
        "INSERT INTO accounts (email, password_hash, password_salt, created_at) VALUES (?, ?, ?, ?)",
        (email, pw_hash, salt, int(time.time())),
    )
    conn.commit()
    row = conn.execute("SELECT id FROM accounts WHERE email = ?", (email,)).fetchone()
    conn.close()
    token = _create_session(email)
    return {"access_token": token, "user_id": row[0], "email": email}


@app.post("/api/auth/login")
@limiter.limit("10/minute")
async def auth_login(request: Request, body: AuthLoginRequest):
    email = body.email.strip().lower()
    password = body.password
    if not email or not password:
        raise HTTPException(status_code=400, detail="Email and password are required")
    conn = get_db()
    row = conn.execute(
        "SELECT id, password_hash, password_salt FROM accounts WHERE email = ?", (email,)
    ).fetchone()
    conn.close()
    if not row:
        raise HTTPException(status_code=401, detail="Incorrect email or password")
    pw_hash = _hash_password(password, row[2])
    if pw_hash != row[1]:
        raise HTTPException(status_code=401, detail="Incorrect email or password")
    token = _create_session(email)
    return {"access_token": token, "user_id": row[0], "email": email}


@app.post("/api/auth/session")
@limiter.limit("60/minute")
async def auth_session(request: Request, body: AuthSessionRequest):
    email = _get_session_email(body.token)
    if not email:
        raise HTTPException(status_code=401, detail="Session expired or invalid")
    conn = get_db()
    row = conn.execute("SELECT id FROM accounts WHERE email = ?", (email,)).fetchone()
    conn.close()
    user_id = row[0] if row else 0
    return {"email": email, "user_id": user_id, "is_pro": is_email_pro(email)}


@app.post("/api/auth/logout")
@limiter.limit("30/minute")
async def auth_logout(request: Request, body: AuthSessionRequest):
    conn = get_db()
    conn.execute("DELETE FROM auth_sessions WHERE token = ?", (body.token,))
    conn.commit()
    conn.close()
    return {"ok": True}

# ---------------------------------------------------------------------------
# Payment endpoints
# ---------------------------------------------------------------------------

@app.post("/api/payment/create-intent")
@limiter.limit("10/minute")
async def create_payment_intent(request: Request, body: CreateIntentRequest):
    if not stripe.api_key:
        raise HTTPException(status_code=503, detail="Payment processing is not configured")
    email = body.email.strip().lower()
    if not email or "@" not in email:
        raise HTTPException(status_code=400, detail="Valid email is required")
    try:
        intent = stripe.PaymentIntent.create(
            amount=PRICE_CENTS,
            currency="usd",
            receipt_email=email,
            metadata={"email": email, "name": body.name.strip()},
            description="Dishpad Pro — Lifetime",
        )
        return {"client_secret": intent.client_secret, "payment_intent_id": intent.id}
    except stripe.StripeError as e:
        raise HTTPException(status_code=400, detail=str(getattr(e, "user_message", str(e))))


@app.post("/api/pro/activate")
@limiter.limit("10/minute")
async def activate_pro(request: Request, body: ActivateProRequest):
    """Called by frontend after payment succeeds. Verifies with Stripe and creates DB record."""
    if not stripe.api_key:
        raise HTTPException(status_code=503, detail="Payment processing is not configured")

    pi_id = body.payment_intent_id.strip()
    email = body.email.strip().lower()

    conn = get_db()
    existing = conn.execute(
        "SELECT id FROM purchases WHERE stripe_payment_intent = ?", (pi_id,)
    ).fetchone()
    if existing:
        conn.close()
        return {"activated": True, "already_activated": True}

    try:
        intent = stripe.PaymentIntent.retrieve(pi_id)
    except stripe.StripeError as e:
        conn.close()
        raise HTTPException(status_code=400, detail=f"Could not verify payment: {getattr(e, 'user_message', str(e))}")

    if intent.status != "succeeded":
        conn.close()
        raise HTTPException(status_code=402, detail=f"Payment not completed (status: {intent.status})")

    license_key = f"CC-{uuid.uuid4().hex[:4].upper()}-{uuid.uuid4().hex[:4].upper()}-{uuid.uuid4().hex[:4].upper()}"
    name = body.name.strip() or (intent.metadata or {}).get("name", "")

    try:
        conn.execute(
            """INSERT INTO purchases (license_key, email, name, stripe_payment_intent, amount_cents, created_at)
               VALUES (?, ?, ?, ?, ?, ?)""",
            (license_key, email, name, pi_id, intent.amount, int(time.time())),
        )
        conn.commit()
    except Exception:
        conn.close()
        raise HTTPException(status_code=500, detail="Failed to activate Pro")

    conn.close()
    asyncio.create_task(asyncio.get_event_loop().run_in_executor(None, send_receipt_email, email, name))
    return {"activated": True, "already_activated": False}


@app.post("/api/pro/check")
@limiter.limit("30/minute")
async def check_pro_status(request: Request, body: CheckProRequest):
    email = body.email.strip().lower()
    if not email:
        return {"is_pro": False}
    return {"is_pro": is_email_pro(email)}


@app.post("/api/license/validate")
@limiter.limit("30/minute")
async def validate_license(request: Request, body: ValidateLicenseRequest):
    key = body.license_key.strip().upper()
    conn = get_db()
    row = conn.execute(
        "SELECT is_revoked, email FROM purchases WHERE license_key = ?", (key,)
    ).fetchone()
    conn.close()
    if not row:
        return {"valid": False}
    if row["is_revoked"]:
        return {"valid": False, "reason": "revoked"}
    return {"valid": True, "email": row["email"]}


@app.post("/api/webhook/stripe")
async def stripe_webhook(request: Request):
    payload    = await request.body()
    sig_header = request.headers.get("stripe-signature", "")
    if not WEBHOOK_SECRET:
        return {"received": True}
    try:
        event = stripe.Webhook.construct_event(payload, sig_header, WEBHOOK_SECRET)
    except stripe.SignatureVerificationError:
        raise HTTPException(status_code=400, detail="Invalid webhook signature")

    if event["type"] == "payment_intent.succeeded":
        intent = event["data"]["object"]
        pi_id  = intent["id"]
        email  = (intent.get("receipt_email") or (intent.get("metadata") or {}).get("email", "")).strip().lower()
        name   = (intent.get("metadata") or {}).get("name", "")
        if email:
            conn = get_db()
            existing = conn.execute(
                "SELECT id FROM purchases WHERE stripe_payment_intent = ?", (pi_id,)
            ).fetchone()
            if not existing:
                license_key = f"CC-{uuid.uuid4().hex[:4].upper()}-{uuid.uuid4().hex[:4].upper()}-{uuid.uuid4().hex[:4].upper()}"
                try:
                    conn.execute(
                        """INSERT INTO purchases (license_key, email, name, stripe_payment_intent, amount_cents, created_at)
                           VALUES (?, ?, ?, ?, ?, ?)""",
                        (license_key, email, name, pi_id, intent.get("amount", PRICE_CENTS), int(time.time())),
                    )
                    conn.commit()
                    asyncio.create_task(asyncio.get_event_loop().run_in_executor(None, send_receipt_email, email, name))
                except Exception:
                    pass
            conn.close()
    return {"received": True}

# ---------------------------------------------------------------------------
# Admin endpoints
# ---------------------------------------------------------------------------

@app.get("/admin/api/stats")
async def admin_stats(x_admin_password: Optional[str] = Header(None)):
    require_admin(x_admin_password)

    conn = get_db()
    rows = conn.execute(
        "SELECT amount_cents, created_at FROM purchases WHERE is_revoked = 0"
    ).fetchall()
    conn.close()

    now = datetime.now(timezone.utc)
    month_key = now.strftime("%Y-%m")

    total_revenue = sum(r["amount_cents"] for r in rows)
    total_customers = len(rows)

    this_month = [
        r for r in rows
        if datetime.fromtimestamp(r["created_at"], tz=timezone.utc).strftime("%Y-%m") == month_key
    ]

    monthly: dict = {}
    for r in rows:
        mk = datetime.fromtimestamp(r["created_at"], tz=timezone.utc).strftime("%Y-%m")
        if mk not in monthly:
            monthly[mk] = {"revenueCents": 0, "customers": 0}
        monthly[mk]["revenueCents"] += r["amount_cents"]
        monthly[mk]["customers"]   += 1

    monthly_revenue = [
        {"month": k, "revenueCents": v["revenueCents"], "customers": v["customers"]}
        for k, v in sorted(monthly.items())
    ][-12:]

    return {
        "totalRevenueCents":     total_revenue,
        "totalCustomers":        total_customers,
        "thisMonthRevenueCents": sum(r["amount_cents"] for r in this_month),
        "thisMonthCustomers":    len(this_month),
        "monthlyRevenue":        monthly_revenue,
    }


@app.get("/admin/api/customers")
async def admin_customers(
    page: int = 1,
    pageSize: int = 25,
    search: str = "",
    x_admin_password: Optional[str] = Header(None),
):
    require_admin(x_admin_password)

    conn = get_db()
    base = "FROM purchases"
    params: list = []
    if search:
        base += " WHERE (email LIKE ? OR name LIKE ? OR license_key LIKE ?)"
        like = f"%{search}%"
        params = [like, like, like]

    total = conn.execute(f"SELECT COUNT(*) {base}", params).fetchone()[0]
    offset = (page - 1) * pageSize
    rows = conn.execute(
        f"SELECT id, license_key, email, name, amount_cents, created_at, is_revoked "
        f"{base} ORDER BY created_at DESC LIMIT ? OFFSET ?",
        params + [pageSize, offset],
    ).fetchall()
    conn.close()

    customers = [
        {
            "id":          r["id"],
            "licenseKey":  r["license_key"],
            "email":       r["email"],
            "name":        r["name"] or "",
            "amountCents": r["amount_cents"],
            "createdAt":   r["created_at"],
            "isRevoked":   bool(r["is_revoked"]),
        }
        for r in rows
    ]
    return {"customers": customers, "total": total, "page": page, "pageSize": pageSize}


@app.get("/admin/api/customers/export")
async def admin_export(
    password: str = "",
    x_admin_password: Optional[str] = Header(None),
):
    require_admin(x_admin_password or password)
    conn = get_db()
    rows = conn.execute(
        "SELECT id, license_key, email, name, amount_cents, created_at, is_revoked "
        "FROM purchases ORDER BY created_at DESC"
    ).fetchall()
    conn.close()

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["ID", "License Key", "Email", "Name", "Amount ($)", "Date", "Status"])
    for r in rows:
        writer.writerow([
            r["id"], r["license_key"], r["email"], r["name"] or "",
            f"{r['amount_cents'] / 100:.2f}",
            datetime.fromtimestamp(r["created_at"], tz=timezone.utc).strftime("%Y-%m-%d"),
            "Revoked" if r["is_revoked"] else "Active",
        ])
    output.seek(0)
    return StreamingResponse(
        iter([output.getvalue()]),
        media_type="text/csv",
        headers={"Content-Disposition": "attachment; filename=dishpad-customers.csv"},
    )


@app.post("/admin/api/customers/revoke")
async def admin_revoke(body: RevokeRequest, x_admin_password: Optional[str] = Header(None)):
    require_admin(x_admin_password)
    conn = get_db()
    conn.execute("UPDATE purchases SET is_revoked = 1 WHERE license_key = ?", (body.licenseKey,))
    conn.commit()
    conn.close()
    return {"revoked": True}


@app.post("/admin/api/customers/restore")
async def admin_restore(body: RevokeRequest, x_admin_password: Optional[str] = Header(None)):
    require_admin(x_admin_password)
    conn = get_db()
    conn.execute("UPDATE purchases SET is_revoked = 0 WHERE license_key = ?", (body.licenseKey,))
    conn.commit()
    conn.close()
    return {"restored": True}


@app.post("/admin/api/send-update")
async def admin_send_update(
    body: SendUpdateRequest,
    x_admin_password: Optional[str] = Header(None),
):
    require_admin(x_admin_password)
    if not body.subject.strip() or not body.body.strip():
        raise HTTPException(status_code=400, detail="Subject and body are required")
    if not SMTP_HOST or not SMTP_USER or not SMTP_PASSWORD:
        raise HTTPException(status_code=503, detail="Email (SMTP) is not configured")

    conn = get_db()
    rows = conn.execute("SELECT email FROM purchases WHERE is_revoked = 0").fetchall()
    conn.close()

    emails = list({r["email"] for r in rows})
    if not emails:
        return {"sent": 0}

    sent = send_bulk_email(emails, body.subject.strip(), body.body.strip())
    return {"sent": sent}


@app.post("/admin/api/test/grant-pro")
async def test_grant_pro(body: EmailRequest, x_admin_password: Optional[str] = Header(None)):
    """Dev only — grant Pro without payment."""
    require_admin(x_admin_password)
    email = body.email.strip().lower()
    conn = get_db()
    existing = conn.execute(
        "SELECT id FROM purchases WHERE email = ? AND is_revoked = 0", (email,)
    ).fetchone()
    if existing:
        conn.close()
        return {"granted": True, "already_pro": True}
    key = f"CC-{uuid.uuid4().hex[:4].upper()}-{uuid.uuid4().hex[:4].upper()}-TEST"
    conn.execute(
        """INSERT INTO purchases (license_key, email, name, stripe_payment_intent, amount_cents, created_at)
           VALUES (?, ?, ?, ?, ?, ?)""",
        (key, email, "Test Grant", f"test_{uuid.uuid4().hex}", 0, int(time.time())),
    )
    conn.commit()
    conn.close()
    return {"granted": True, "already_pro": False}


# ===========================================================================
# RECIPE EXTRACTION
# ===========================================================================

RECIPE_SCHEMA = {
    "type": "object",
    "properties": {
        "title": {"type": "string"},
        "ingredients": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "original": {"type": "string"},
                    "name":     {"type": "string"},
                    "amount":   {"anyOf": [{"type": "number"}, {"type": "null"}]},
                    "unit":     {"anyOf": [{"type": "string"}, {"type": "null"}]},
                },
                "required": ["original", "name", "amount", "unit"],
                "additionalProperties": False,
            },
        },
        "steps":        {"type": "array", "items": {"type": "string"}},
        "prepTime":     {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "cookTime":     {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "totalTime":    {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "baseServings": {"type": "integer"},
    },
    "required": ["title", "ingredients", "steps", "baseServings"],
    "additionalProperties": False,
}

RECIPE_ITEM_SCHEMA = {
    "type": "object",
    "properties": {
        "title": {"type": "string"},
        "ingredients": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "original": {"type": "string"},
                    "name":     {"type": "string"},
                    "amount":   {"anyOf": [{"type": "number"}, {"type": "null"}]},
                    "unit":     {"anyOf": [{"type": "string"}, {"type": "null"}]},
                },
                "required": ["original", "name", "amount", "unit"],
                "additionalProperties": False,
            },
        },
        "steps":        {"type": "array", "items": {"type": "string"}},
        "prepTime":     {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "cookTime":     {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "totalTime":    {"anyOf": [{"type": "integer"}, {"type": "null"}]},
        "baseServings": {"type": "integer"},
    },
    "required": ["title", "ingredients", "steps", "baseServings"],
    "additionalProperties": False,
}

MULTI_RECIPE_SCHEMA = {
    "type": "object",
    "properties": {
        "recipes": {"type": "array", "items": RECIPE_ITEM_SCHEMA},
    },
    "required": ["recipes"],
    "additionalProperties": False,
}

SUPPORTED_MEDIA_TYPES = {"image/jpeg", "image/png", "image/webp", "image/gif"}

# ---------------------------------------------------------------------------
# HTML / text utilities
# ---------------------------------------------------------------------------

def extract_page_text(html: str) -> str:
    soup = BeautifulSoup(html, "lxml")
    for tag in soup(["script", "style", "nav", "header", "footer", "aside",
                     "iframe", "noscript", "form", "button"]):
        tag.decompose()
    text = soup.get_text(separator="\n", strip=True)
    lines = [l.strip() for l in text.split("\n") if l.strip()]
    return "\n".join(lines)[:50000]


def get_image_url(html: str, url: str) -> Optional[str]:
    try:
        scraper = scrape_html(html, org_url=url)
        return scraper.image()
    except Exception:
        return None


def extract_jsonld_recipe(html: str) -> Optional[dict]:
    soup = BeautifulSoup(html, "lxml")
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.string or "")
        except Exception:
            continue
        if isinstance(data, dict) and "@graph" in data:
            for item in data["@graph"]:
                t = item.get("@type", "")
                if (isinstance(t, list) and "Recipe" in t) or t == "Recipe":
                    return item
        if isinstance(data, dict):
            t = data.get("@type", "")
            if (isinstance(t, list) and "Recipe" in t) or t == "Recipe":
                return data
        if isinstance(data, list):
            for item in data:
                if not isinstance(item, dict):
                    continue
                t = item.get("@type", "")
                if (isinstance(t, list) and "Recipe" in t) or t == "Recipe":
                    return item
    return None


def _parse_iso_duration(val) -> Optional[int]:
    if val is None:
        return None
    if isinstance(val, int):
        return val if val > 0 else None
    m = re.search(r'PT(?:(\d+)H)?(?:(\d+)M)?', str(val))
    if m:
        total = int(m.group(1) or 0) * 60 + int(m.group(2) or 0)
        return total if total > 0 else None
    return None

# ---------------------------------------------------------------------------
# Ingredient parser
# ---------------------------------------------------------------------------

UNIT_PATTERN = re.compile(
    r"^(cups?|tablespoons?|tbsp|teaspoons?|tsp|ounces?|oz|pounds?|lbs?|grams?|g|kg|kilograms?|"
    r"ml|milliliters?|liters?|l|quarts?|qt|pints?|pt|gallons?|gal|pinch|pinches|dash|dashes|"
    r"cloves?|slices?|pieces?|cans?|bottles?|packages?|sticks?|heads?|bunches?|sprigs?|stalks?|whole)$",
    re.IGNORECASE,
)
MIXED_NUMBER   = re.compile(r"^(\d+)\s+(\d+)\s*/\s*(\d+)")
FRACTION       = re.compile(r"^(\d+)\s*/\s*(\d+)")
DECIMAL_OR_INT = re.compile(r"^(\d+\.?\d*)")
UNICODE_FRACTIONS = {
    "\u00bc": 0.25, "\u00bd": 0.5, "\u00be": 0.75,
    "\u2153": 0.333, "\u2154": 0.667,
    "\u2155": 0.2, "\u2156": 0.4, "\u2157": 0.6, "\u2158": 0.8,
    "\u2159": 0.167, "\u215a": 0.833,
    "\u215b": 0.125, "\u215c": 0.375, "\u215d": 0.625, "\u215e": 0.875,
}


def parse_ingredient(raw: str) -> dict:
    text = raw.strip()
    if not text:
        return {"original": raw, "name": "", "amount": None, "unit": None}
    amount = None
    unit = None
    rest = text
    if rest and rest[0] in UNICODE_FRACTIONS:
        amount = UNICODE_FRACTIONS[rest[0]]
        rest = rest[1:].strip()
    else:
        m = MIXED_NUMBER.match(rest)
        if m:
            amount = int(m.group(1)) + int(m.group(2)) / int(m.group(3))
            rest = rest[m.end():].strip()
        else:
            m = FRACTION.match(rest)
            if m:
                den = int(m.group(2))
                amount = int(m.group(1)) / den if den != 0 else 0.0
                rest = rest[m.end():].strip()
            else:
                m = DECIMAL_OR_INT.match(rest)
                if m:
                    amount = float(m.group(1))
                    rest = rest[m.end():].strip()
                    if rest and rest[0] in UNICODE_FRACTIONS:
                        amount += UNICODE_FRACTIONS[rest[0]]
                        rest = rest[1:].strip()
    words = rest.split(None, 1)
    if words and UNIT_PATTERN.match(words[0].rstrip(".,;")):
        unit = words[0].rstrip(".,;").lower()
        rest = words[1] if len(words) > 1 else ""
    name = rest.strip().lstrip("of ").strip().lstrip(",;- ").strip()
    return {"original": raw, "name": name if name else raw.strip(), "amount": amount, "unit": unit}

# ---------------------------------------------------------------------------
# JSON-LD → ClipResult
# ---------------------------------------------------------------------------

def jsonld_to_clipresult(recipe: dict) -> dict:
    title = recipe.get("name") or "Untitled Recipe"
    raw_ingredients = recipe.get("recipeIngredient") or []
    ingredients = [parse_ingredient(i) for i in raw_ingredients if isinstance(i, str) and i.strip()]
    raw_instructions = recipe.get("recipeInstructions") or []
    steps: list = []
    if isinstance(raw_instructions, str):
        steps = [s.strip() for s in raw_instructions.split("\n") if s.strip()]
    elif isinstance(raw_instructions, list):
        for item in raw_instructions:
            if isinstance(item, str) and item.strip():
                steps.append(item.strip())
            elif isinstance(item, dict):
                if item.get("@type") == "HowToSection":
                    for sub in item.get("itemListElement") or []:
                        text = (sub.get("text") or sub.get("name") or "").strip()
                        if text:
                            steps.append(text)
                else:
                    text = (item.get("text") or item.get("name") or "").strip()
                    if text:
                        steps.append(text)
    yields = recipe.get("recipeYield")
    servings = 4
    if yields:
        if isinstance(yields, int):
            servings = yields
        else:
            if isinstance(yields, list) and yields:
                yields = yields[0]
            if isinstance(yields, str):
                m = re.search(r'\d+', yields)
                if m:
                    servings = int(m.group())
    image = recipe.get("image")
    image_url: Optional[str] = None
    if isinstance(image, str):
        image_url = image
    elif isinstance(image, list) and image:
        first = image[0]
        image_url = first if isinstance(first, str) else (first.get("url") if isinstance(first, dict) else None)
    elif isinstance(image, dict):
        image_url = image.get("url")
    return {
        "title": title, "ingredients": ingredients, "steps": steps,
        "prepTime": _parse_iso_duration(recipe.get("prepTime")),
        "cookTime": _parse_iso_duration(recipe.get("cookTime")),
        "totalTime": _parse_iso_duration(recipe.get("totalTime")),
        "baseServings": servings, "imageUrl": image_url,
    }

# ---------------------------------------------------------------------------
# recipe-scrapers fallback
# ---------------------------------------------------------------------------

def _scraper_to_dict(scraper) -> dict:
    try:
        title = scraper.title()
    except Exception:
        title = "Untitled Recipe"
    try:
        raw_ingredients = scraper.ingredients()
    except Exception:
        raw_ingredients = []
    try:
        raw_steps = scraper.instructions_list()
        if not raw_steps:
            raw_steps = [s.strip() for s in scraper.instructions().split("\n") if s.strip()]
    except Exception:
        raw_steps = []
    try:
        prep_time = scraper.prep_time()
    except Exception:
        prep_time = None
    try:
        cook_time = scraper.cook_time()
    except Exception:
        cook_time = None
    try:
        total_time = scraper.total_time()
    except Exception:
        total_time = None
    try:
        servings_raw = scraper.yields()
        servings = int(re.search(r"\d+", servings_raw).group()) if servings_raw else 4
    except Exception:
        servings = 4
    return {
        "title": title,
        "ingredients": [parse_ingredient(i) for i in raw_ingredients],
        "steps": raw_steps, "prepTime": prep_time, "cookTime": cook_time,
        "totalTime": total_time, "baseServings": servings,
    }


def extract_with_scrapers(html: str, url: str) -> dict:
    for wild in (False, True):
        try:
            scraper = scrape_html(html, org_url=url, wild_mode=wild) if wild else scrape_html(html, org_url=url)
            result = _scraper_to_dict(scraper)
            if result.get("ingredients") or result.get("steps"):
                return result
        except Exception:
            pass
    raise ValueError("No recipe content found")

# ---------------------------------------------------------------------------
# Claude — web recipe extraction
# ---------------------------------------------------------------------------

EXTRACTION_PROMPT = """You are a precise recipe extraction AI. Extract the complete recipe from this webpage text.

ACCURACY RULES:
1. Copy ingredient names VERBATIM as they appear on the page.
2. Fraction accuracy: 1/4=0.25, 1/3=0.333, 1/2=0.5, 2/3=0.667, 3/4=0.75.
3. Extract EVERY ingredient and EVERY step — nothing is optional.
4. If the page has multiple recipes, extract only the main/featured one.
5. "name" = the ingredient noun only, without amount, unit, or prep notes.
6. Times in minutes as integers, or null if not stated.
7. "baseServings": parse from "serves X" or similar. Default 4 if absent.

Return ONLY valid JSON — no markdown fences, no extra text."""


def extract_with_claude(page_text: str, url: str, jsonld_hint: Optional[str] = None) -> dict:
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        raise RuntimeError("ANTHROPIC_API_KEY is not set")
    client = anthropic.Anthropic(api_key=api_key)
    parts = []
    if jsonld_hint:
        parts.append(f"STRUCTURED RECIPE DATA (JSON-LD — use this first):\n{jsonld_hint}")
    parts.append(f"FULL PAGE TEXT:\n{page_text}")
    combined = "\n\n---\n\n".join(parts)
    response = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=4096,
        messages=[{"role": "user", "content": f"{EXTRACTION_PROMPT}\n\nPage URL: {url}\n\n{combined}"}],
        output_config={"format": {"type": "json_schema", "schema": RECIPE_SCHEMA}},
    )
    text_block = next((b.text for b in response.content if b.type == "text"), "")
    return json.loads(text_block)

# ---------------------------------------------------------------------------
# Claude — photo extraction
# ---------------------------------------------------------------------------

PHOTO_EXTRACTION_PROMPT = """You are a precise recipe extraction AI analyzing a photograph of a recipe.

ACCURACY RULES:
1. Extract EVERY ingredient with its exact stated amount.
2. Fraction accuracy: 1/4=0.25, 1/3=0.333, 1/2=0.5, 2/3=0.667, 3/4=0.75.
3. "original" = the complete ingredient line exactly as written.
4. "name" = the ingredient noun only — strip amount, unit, and prep notes.
5. Steps: transcribe each instruction faithfully.
6. Times in minutes as integers, null if not shown.
7. "baseServings": from "serves/makes/yields X". Default 4 if not stated.

Return ONLY valid JSON — no markdown fences, no extra text."""


def extract_photo_with_claude(image_b64: str, media_type: str) -> dict:
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        raise RuntimeError("ANTHROPIC_API_KEY is not set")
    client = anthropic.Anthropic(api_key=api_key)
    response = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=4096,
        messages=[{
            "role": "user",
            "content": [
                {"type": "image", "source": {"type": "base64", "media_type": media_type, "data": image_b64}},
                {"type": "text", "text": PHOTO_EXTRACTION_PROMPT},
            ],
        }],
        output_config={"format": {"type": "json_schema", "schema": RECIPE_SCHEMA}},
    )
    text_block = next((b.text for b in response.content if b.type == "text"), "")
    return json.loads(text_block)

# ---------------------------------------------------------------------------
# YouTube helpers
# ---------------------------------------------------------------------------

_YT_ID_RE = re.compile(
    r'(?:youtube\.com/(?:watch\?(?:.*&)?v=|shorts/|embed/|v/)|youtu\.be/)'
    r'([a-zA-Z0-9_-]{11})',
    re.IGNORECASE,
)


def extract_youtube_video_id(url: str) -> Optional[str]:
    m = _YT_ID_RE.search(url)
    return m.group(1) if m else None


def is_youtube_url(url: str) -> bool:
    return extract_youtube_video_id(url) is not None


def get_youtube_thumbnail(video_id: str) -> str:
    return f"https://img.youtube.com/vi/{video_id}/maxresdefault.jpg"


def _ensure_ffmpeg_on_path() -> None:
    import shutil
    if shutil.which("ffmpeg"):
        return
    try:
        import static_ffmpeg
        static_ffmpeg.add_paths()
    except Exception:
        pass


def _fetch_youtube_description_via_api(video_id: str) -> dict:
    """Use YouTube Data API v3 to get title and description. Works from any IP."""
    if not YOUTUBE_API_KEY:
        return {}
    try:
        import urllib.request
        import urllib.parse
        params = urllib.parse.urlencode({
            "id": video_id, "part": "snippet", "key": YOUTUBE_API_KEY,
        })
        req = urllib.request.urlopen(
            f"https://www.googleapis.com/youtube/v3/videos?{params}", timeout=10
        )
        data = json.loads(req.read())
        items = data.get("items", [])
        if not items:
            return {}
        snippet = items[0].get("snippet", {})
        return {
            "title": snippet.get("title", ""),
            "description": snippet.get("description", ""),
            "thumbnail": (snippet.get("thumbnails", {}).get("high", {}) or
                          snippet.get("thumbnails", {}).get("medium", {}) or {}).get("url", ""),
            "chapters": [],
        }
    except Exception as exc:
        print(f"[Dishpad] YouTube Data API failed: {exc}")
        return {}


def _fetch_youtube_metadata_sync(url: str) -> dict:
    # Try YouTube Data API v3 first (works from any IP including cloud)
    video_id_match = re.search(r"(?:v=|youtu\.be/)([A-Za-z0-9_-]{11})", url)
    if video_id_match and YOUTUBE_API_KEY:
        result = _fetch_youtube_description_via_api(video_id_match.group(1))
        if result.get("title"):
            return result
    # Fall back to yt-dlp
    try:
        import yt_dlp
        ydl_opts = {
            "quiet": True, "no_warnings": True, "noplaylist": True, "skip_download": True,
            "extractor_args": {"youtube": {"player_client": ["web", "mweb", "android"]}},
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
        return {
            "title": info.get("title") or "", "description": info.get("description") or "",
            "chapters": info.get("chapters") or [], "thumbnail": info.get("thumbnail") or "",
        }
    except Exception as exc:
        print(f"[Dishpad] yt-dlp metadata failed: {exc}")
        return {}


async def fetch_youtube_metadata(url: str) -> dict:
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, _fetch_youtube_metadata_sync, url)


def _extract_youtube_frames_sync(url: str, n_frames: int = 8) -> list:
    import subprocess as _sp, tempfile, base64, shutil
    _ensure_ffmpeg_on_path()
    if not shutil.which("ffmpeg") or not shutil.which("ffprobe"):
        return []
    try:
        import yt_dlp
    except ImportError:
        return []
    try:
        with tempfile.TemporaryDirectory() as tmpdir:
            video_path = os.path.join(tmpdir, "v.mp4")
            ydl_opts = {
                "quiet": True, "no_warnings": True, "noplaylist": True,
                "format": "worstvideo[ext=mp4]/worstvideo/worst[ext=mp4]/worst",
                "outtmpl": video_path,
                "external_downloader": "ffmpeg",
                "external_downloader_args": {"ffmpeg_i": ["-t", "180"]},
                "extractor_args": {"youtube": {"player_client": ["web", "mweb", "android"]}},
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            if not os.path.exists(video_path) or os.path.getsize(video_path) < 5000:
                return []
            probe = _sp.run(
                ["ffprobe", "-v", "quiet", "-show_entries", "format=duration", "-of", "csv=p=0", video_path],
                capture_output=True, text=True, timeout=10,
            )
            try:
                duration = min(float(probe.stdout.strip()), 180)
            except Exception:
                duration = 180
            interval = max(duration / n_frames, 1)
            frames: list = []
            for i in range(n_frames):
                ts = interval * i
                frame_path = os.path.join(tmpdir, f"f{i}.jpg")
                _sp.run(
                    ["ffmpeg", "-ss", str(ts), "-i", video_path,
                     "-frames:v", "1", "-q:v", "5", "-vf", "scale=640:-2", frame_path, "-y"],
                    capture_output=True, timeout=15,
                )
                if os.path.exists(frame_path) and os.path.getsize(frame_path) > 200:
                    with open(frame_path, "rb") as f:
                        frames.append(base64.b64encode(f.read()).decode())
            return frames
    except Exception as exc:
        print(f"[Dishpad] Frame extraction failed: {exc}")
        return []


async def extract_youtube_frames(url: str) -> list:
    loop = asyncio.get_event_loop()
    try:
        return await asyncio.wait_for(
            loop.run_in_executor(None, partial(_extract_youtube_frames_sync, url)),
            timeout=30.0,
        )
    except (asyncio.TimeoutError, Exception):
        return []


def _fetch_transcript_sync(video_id: str) -> Optional[str]:
    try:
        from youtube_transcript_api import (
            YouTubeTranscriptApi, NoTranscriptFound, TranscriptsDisabled, CouldNotRetrieveTranscript,
        )
        api = YouTubeTranscriptApi()
        fetched = None
        try:
            fetched = api.fetch(video_id, languages=["en", "en-US", "en-GB", "en-CA", "en-AU"])
        except NoTranscriptFound:
            pass
        if fetched is None:
            try:
                transcript_list = api.list(video_id)
                best = None
                for t in transcript_list:
                    if best is None or (not t.is_generated and best.is_generated):
                        best = t
                if best is not None:
                    fetched = best.fetch()
            except Exception:
                pass
        if not fetched:
            return None
        text = " ".join(s.text if hasattr(s, "text") else s.get("text", "") for s in fetched)
        text = re.sub(r"\[(?:[^\]]*)\]", "", text)
        text = re.sub(r"♪[^♪]*♪", "", text)
        text = re.sub(r"\s+", " ", text).strip()
        return text[:50000] if text else None
    except Exception:
        return None


async def fetch_youtube_transcript(video_id: str) -> Optional[str]:
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, partial(_fetch_transcript_sync, video_id))


def get_youtube_page_info(html: str) -> dict:
    result: dict = {"title": None, "description": None}
    soup = BeautifulSoup(html, "lxml")
    og_title = soup.find("meta", property="og:title")
    if og_title:
        result["title"] = og_title.get("content", "").strip() or None
    for script in soup.find_all("script"):
        raw = script.string or ""
        if "ytInitialPlayerResponse" not in raw:
            continue
        match = re.search(r"ytInitialPlayerResponse\s*=\s*(\{)", raw)
        if not match:
            continue
        try:
            decoder = json.JSONDecoder()
            obj, _ = decoder.raw_decode(raw[match.start(1):])
            video_details = obj.get("videoDetails", {})
            desc = video_details.get("shortDescription", "")
            if desc:
                result["description"] = desc
            if not result["title"]:
                result["title"] = video_details.get("title", "").strip() or None
            break
        except (json.JSONDecodeError, ValueError):
            continue
    if not result["description"]:
        og_desc = soup.find("meta", property="og:description")
        if og_desc:
            result["description"] = og_desc.get("content", "").strip() or None
    return result


YOUTUBE_EXTRACTION_PROMPT = """\
You are an expert recipe extraction AI analyzing a YouTube cooking video.

MULTIPLE RECIPES: Many videos contain multiple recipes. Return ALL in the "recipes" array.
Each recipe must have its own complete ingredient list and steps.

SOURCE PRIORITY:
1. VIDEO DESCRIPTION — highest priority if it has a written recipe.
2. VIDEO CHAPTERS — tells you where each recipe starts.
3. VIDEO TRANSCRIPT — interpret spoken measurements naturally.
4. VIDEO FRAMES — look for on-screen ingredient cards or text overlays.

ACCURACY RULES:
- Extract EVERY ingredient with amount, unit, name.
- Times as integers in minutes. baseServings default 4.
- DO NOT invent recipes. If no recipe content at all, return empty array."""


def extract_youtube_with_claude(
    video_id: str, title: Optional[str], description: Optional[str],
    transcript: Optional[str], url: str,
    chapters: Optional[list] = None, frames: Optional[list] = None,
) -> list:
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        raise RuntimeError("ANTHROPIC_API_KEY is not set")
    parts: list[str] = []
    if title:
        parts.append(f"VIDEO TITLE:\n{title}")
    if chapters:
        ch_text = "\n".join(
            f"  {c.get('title','?')} — {int(c.get('start_time',0)//60)}:{int(c.get('start_time',0)%60):02d}"
            for c in chapters
        )
        parts.append(f"VIDEO CHAPTERS:\n{ch_text}")
    if description:
        parts.append(f"VIDEO DESCRIPTION (creator-written — highest priority):\n{description[:12000]}")
    if transcript:
        parts.append(f"VIDEO TRANSCRIPT (auto-generated):\n{transcript}")
    combined = "\n\n---\n\n".join(parts)
    client = anthropic.Anthropic(api_key=api_key)
    if frames:
        content: list = [{"type": "text", "text": f"{YOUTUBE_EXTRACTION_PROMPT}\n\nVideo URL: {url}\n\n{combined}"}]
        for frame_b64 in frames[:8]:
            content.append({"type": "image", "source": {"type": "base64", "media_type": "image/jpeg", "data": frame_b64}})
        content.append({"type": "text", "text": "Images above are frames from the first 3 minutes of the video."})
    else:
        content = f"{YOUTUBE_EXTRACTION_PROMPT}\n\nVideo URL: {url}\n\n{combined}"
    response = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=8192,
        messages=[{"role": "user", "content": content}],
        output_config={"format": {"type": "json_schema", "schema": MULTI_RECIPE_SCHEMA}},
    )
    text_block = next((b.text for b in response.content if b.type == "text"), "")
    data = json.loads(text_block)
    return data.get("recipes", [])

# ---------------------------------------------------------------------------
# TikTok / Instagram helpers
# ---------------------------------------------------------------------------

def is_tiktok_url(url: str) -> bool:
    return bool(re.search(r'tiktok\.com|vm\.tiktok\.com', url, re.I))


def is_instagram_url(url: str) -> bool:
    return bool(re.search(r'instagram\.com', url, re.I))


def is_pinterest_url(url: str) -> bool:
    return bool(re.search(r'pinterest\.com|pin\.it', url, re.I))


def _fetch_social_metadata_html(url: str) -> dict:
    """Fallback: scrape og: tags or TikTok oEmbed when yt-dlp fails."""
    import urllib.request as _ur, ssl as _ssl, json as _json
    ctx = _ssl.create_default_context()
    mobile_ua = (
        "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
        "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1"
    )
    # TikTok: oEmbed API works from any IP and returns description/title
    if "tiktok" in url.lower():
        try:
            import urllib.parse
            oembed_url = "https://www.tiktok.com/oembed?url=" + urllib.parse.quote(url, safe="")
            req = _ur.Request(oembed_url, headers={"User-Agent": "Mozilla/5.0"})
            with _ur.urlopen(req, timeout=10, context=ctx) as r:
                data = _json.loads(r.read())
            title = data.get("title") or data.get("author_name") or ""
            return {"title": title, "description": title, "thumbnail": data.get("thumbnail_url") or ""}
        except Exception as e:
            print(f"[Dishpad] TikTok oEmbed fallback failed: {e}")
    # Generic og: tags fallback
    try:
        req = _ur.Request(url, headers={"User-Agent": mobile_ua, "Accept-Language": "en-US,en;q=0.9"})
        with _ur.urlopen(req, timeout=15, context=ctx) as r:
            html = r.read().decode("utf-8", errors="ignore")
        from bs4 import BeautifulSoup as _BS
        soup = _BS(html, "html.parser")
        def _og(prop: str) -> str:
            tag = soup.find("meta", {"property": f"og:{prop}"})
            return (tag.get("content") or "") if tag else ""
        return {"title": _og("title"), "description": _og("description"), "thumbnail": _og("image")}
    except Exception as e:
        print(f"[Dishpad] og: tag fallback failed: {e}")
    return {}


def _fetch_social_metadata_sync(url: str) -> dict:
    try:
        import yt_dlp
        ydl_opts = {"quiet": True, "no_warnings": True, "noplaylist": True,
                    "skip_download": True, "socket_timeout": 20}
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
        return {
            "title": info.get("title") or "", "description": info.get("description") or "",
            "thumbnail": info.get("thumbnail") or "", "uploader": info.get("uploader") or "",
        }
    except Exception as exc:
        print(f"[Dishpad] yt-dlp social metadata failed: {exc}")
        return _fetch_social_metadata_html(url)


async def fetch_social_metadata(url: str) -> dict:
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, _fetch_social_metadata_sync, url)


def _extract_social_frames_sync(url: str, n_frames: int = 6) -> list:
    import subprocess as _sp, tempfile, base64, shutil
    _ensure_ffmpeg_on_path()
    if not shutil.which("ffmpeg"):
        return []
    try:
        import yt_dlp
    except ImportError:
        return []
    try:
        with tempfile.TemporaryDirectory() as tmpdir:
            video_path = os.path.join(tmpdir, "v.mp4")
            ydl_opts = {
                "quiet": True, "no_warnings": True, "noplaylist": True,
                "format": "worstvideo[ext=mp4]/worstvideo/worst[ext=mp4]/worst",
                "outtmpl": video_path, "socket_timeout": 20,
                "external_downloader": "ffmpeg",
                "external_downloader_args": {"ffmpeg_i": ["-t", "90"]},
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            if not os.path.exists(video_path) or os.path.getsize(video_path) < 5000:
                return []
            probe = _sp.run(
                ["ffprobe", "-v", "quiet", "-show_entries", "format=duration", "-of", "csv=p=0", video_path],
                capture_output=True, text=True, timeout=10,
            )
            try:
                duration = min(float(probe.stdout.strip()), 90)
            except Exception:
                duration = 90
            interval = max(duration / n_frames, 1)
            frames: list = []
            for i in range(n_frames):
                ts = interval * i
                frame_path = os.path.join(tmpdir, f"f{i}.jpg")
                _sp.run(
                    ["ffmpeg", "-ss", str(ts), "-i", video_path,
                     "-frames:v", "1", "-q:v", "5", "-vf", "scale=640:-2", frame_path, "-y"],
                    capture_output=True, timeout=15,
                )
                if os.path.exists(frame_path) and os.path.getsize(frame_path) > 200:
                    with open(frame_path, "rb") as f:
                        frames.append(base64.b64encode(f.read()).decode())
            return frames
    except Exception as exc:
        print(f"[Dishpad] Social frame extraction failed: {exc}")
        return []


async def extract_social_frames(url: str) -> list:
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, partial(_extract_social_frames_sync, url))


SOCIAL_EXTRACTION_PROMPT = """\
You are a recipe extraction AI analyzing a social media video post (TikTok or Instagram).

MULTIPLE RECIPES: Some posts contain multiple recipes. Return ALL in the "recipes" array.

SOURCE PRIORITY:
1. POST CAPTION/DESCRIPTION — most reliable, use first.
2. VIDEO FRAMES — look for on-screen text, ingredient overlays.
3. VIDEO TITLE — may name the dish.

ACCURACY RULES:
- Extract EVERY ingredient with amount, unit, name.
- Steps: clean actionable instructions — strip hashtags, emojis, promo text.
- Times as integers in minutes. baseServings default 2 for social recipes.
- DO NOT invent recipes. If no recipe content, return empty array."""


def extract_social_with_claude(
    title: Optional[str], description: Optional[str], url: str, frames: Optional[list] = None,
) -> list:
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        raise ValueError("ANTHROPIC_API_KEY not set")
    client = anthropic.Anthropic(api_key=api_key)
    parts = []
    if title:
        parts.append(f"VIDEO TITLE: {title}")
    if description:
        parts.append(f"POST CAPTION/DESCRIPTION:\n{description[:8000]}")
    parts.append(f"URL: {url}")
    text_content: list = [{"type": "text", "text": "\n\n".join(parts)}]
    if frames:
        for b64 in frames[:4]:
            text_content.append({"type": "image", "source": {"type": "base64", "media_type": "image/jpeg", "data": b64}})
    text_content.append({"type": "text", "text": SOCIAL_EXTRACTION_PROMPT})
    response = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=6000,
        messages=[{"role": "user", "content": text_content}],
        output_config={"format": {"type": "json_schema", "schema": MULTI_RECIPE_SCHEMA}},
    )
    text_block = next((b.text for b in response.content if b.type == "text"), "")
    data = json.loads(text_block)
    return data.get("recipes", [])

# ---------------------------------------------------------------------------
# Pinterest helpers
# ---------------------------------------------------------------------------

def _get_pinterest_source_url_sync(pin_url: str) -> Optional[str]:
    m = re.search(r'/pin/(\d+)', pin_url)
    if not m:
        return None
    pin_id = m.group(1)
    try:
        import urllib.request as _ur
        api_url = f"https://widgets.pinterest.com/v3/pidgets/pins/info/?pin_ids={pin_id}"
        req = _ur.Request(api_url, headers={"User-Agent": "curl/7.79.1", "Accept": "application/json"})
        resp = _ur.urlopen(req, timeout=10)
        data = json.loads(resp.read())
        pins = data.get("data", [])
        if isinstance(pins, list) and pins:
            pin = pins[0]
            link = pin.get("link") or pin.get("rich_metadata", {}).get("url", "")
            if link and "pinterest" not in link.lower():
                return link
    except Exception as exc:
        print(f"[Dishpad] Pinterest widgets API failed: {exc}")
    return None


async def get_pinterest_source_url(pin_url: str) -> Optional[str]:
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, _get_pinterest_source_url_sync, pin_url)

# ---------------------------------------------------------------------------
# /api/clip
# ---------------------------------------------------------------------------

@app.post("/api/clip")
@limiter.limit("30/minute")
async def clip_recipe(request: Request, body: ClipRequest):
    url = body.url.strip()
    if not url:
        return {"error": "URL is required"}

    # Rate limiting — free tier gets FREE_CLIPS_PER_DAY per day per IP
    client_ip = get_client_ip(request)
    admin_pw = request.headers.get("x-admin-password", "")
    is_admin = bool(ADMIN_PASSWORD and admin_pw == ADMIN_PASSWORD)
    if not is_admin and not is_email_pro(body.proEmail or ""):
        if not check_and_increment_free_usage(client_ip):
            return {"error": (
                f"You've used your {FREE_CLIPS_PER_DAY} free recipe clips. "
                "Upgrade to Dishpad Pro for unlimited clipping."
            )}

    if not os.environ.get("ANTHROPIC_API_KEY"):
        return {"error": "Recipe AI is not configured. Please try again later."}

    # ---- YouTube ------------------------------------------------------------
    if is_youtube_url(url):
        video_id = extract_youtube_video_id(url)
        gather_results = await asyncio.gather(
            fetch_youtube_transcript(video_id),
            fetch_youtube_metadata(url),
            extract_youtube_frames(url),
            return_exceptions=True,
        )
        transcript = gather_results[0] if not isinstance(gather_results[0], Exception) else None
        yt_meta    = gather_results[1] if not isinstance(gather_results[1], Exception) else {}
        frames     = gather_results[2] if not isinstance(gather_results[2], Exception) else []

        title       = yt_meta.get("title") or None
        description = yt_meta.get("description") or None
        chapters    = yt_meta.get("chapters") or []
        thumbnail   = yt_meta.get("thumbnail") or get_youtube_thumbnail(video_id)

        if not title or not description:
            # Use mobile URL — works from datacenter IPs where desktop URL is blocked
            mobile_url = f"https://m.youtube.com/watch?v={video_id}"
            for _yt_url, _ua in [
                (mobile_url, "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1"),
                (url, "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/124.0 Safari/537.36"),
            ]:
                try:
                    async with httpx.AsyncClient(follow_redirects=True, timeout=15.0, headers={
                        "User-Agent": _ua, "Accept-Language": "en-US,en;q=0.9",
                    }) as hclient:
                        resp = await hclient.get(_yt_url)
                        page_info = get_youtube_page_info(resp.text)
                        title       = title       or page_info.get("title")
                        description = description or page_info.get("description")
                    if title and description:
                        break
                except Exception:
                    pass

        if not transcript and not description and not frames:
            return {"error": "Couldn't find recipe content. Make sure the video is public and has captions or a description."}

        try:
            recipes = extract_youtube_with_claude(
                video_id=video_id, title=title, description=description,
                transcript=transcript, url=url, chapters=chapters, frames=frames or [],
            )
        except Exception as e:
            print(f"[Dishpad] YouTube extraction failed: {e}")
            return {"error": "Couldn't extract a recipe from this video. Try one with clear ingredient lists."}

        if not recipes:
            return {"error": "No recipe was found in this video. Try a cooking tutorial where ingredients and steps are clearly stated."}

        if len(recipes) == 1:
            r = recipes[0]
            return {"title": r.get("title") or title or "Untitled Recipe", "source": url,
                    "imageUrl": thumbnail, "ingredients": r.get("ingredients", []),
                    "steps": r.get("steps", []), "prepTime": r.get("prepTime"),
                    "cookTime": r.get("cookTime"), "totalTime": r.get("totalTime"),
                    "baseServings": r.get("baseServings", 4)}
        return {
            "multipleRecipes": True,
            "recipes": [{"title": r.get("title") or f"Recipe {i+1}", "source": url, "imageUrl": thumbnail,
                         "ingredients": r.get("ingredients", []), "steps": r.get("steps", []),
                         "prepTime": r.get("prepTime"), "cookTime": r.get("cookTime"),
                         "totalTime": r.get("totalTime"), "baseServings": r.get("baseServings", 4)}
                        for i, r in enumerate(recipes)],
        }

    # ---- TikTok / Instagram -------------------------------------------------
    if is_tiktok_url(url) or is_instagram_url(url):
        platform_name = "TikTok" if is_tiktok_url(url) else "Instagram"
        gather_results = await asyncio.gather(
            fetch_social_metadata(url),
            extract_social_frames(url),
            return_exceptions=True,
        )
        social_meta = gather_results[0] if not isinstance(gather_results[0], Exception) else {}
        frames      = gather_results[1] if not isinstance(gather_results[1], Exception) else []
        title       = social_meta.get("title") or None
        description = social_meta.get("description") or None
        thumbnail   = social_meta.get("thumbnail") or None

        if not title and not description and not frames:
            return {"error": (
                f"Couldn't access this {platform_name} video. Make sure the post is public. "
                "If the recipe is in the caption, copy it and add manually, "
                "or take a screenshot and use Scan Photo."
            )}

        try:
            recipes = extract_social_with_claude(title=title, description=description, url=url, frames=frames or [])
        except Exception as e:
            print(f"[Dishpad] {platform_name} extraction failed: {e}")
            return {"error": f"Couldn't extract a recipe from this {platform_name} video."}

        if not recipes:
            return {"error": f"No recipe was found in this {platform_name} post. Try a post where the recipe is written in the caption."}

        if len(recipes) == 1:
            r = recipes[0]
            return {"title": r.get("title") or title or "Untitled Recipe", "source": url,
                    "imageUrl": thumbnail, "ingredients": r.get("ingredients", []),
                    "steps": r.get("steps", []), "prepTime": r.get("prepTime"),
                    "cookTime": r.get("cookTime"), "totalTime": r.get("totalTime"),
                    "baseServings": r.get("baseServings", 2)}
        return {
            "multipleRecipes": True,
            "recipes": [{"title": r.get("title") or f"Recipe {i+1}", "source": url, "imageUrl": thumbnail,
                         "ingredients": r.get("ingredients", []), "steps": r.get("steps", []),
                         "prepTime": r.get("prepTime"), "cookTime": r.get("cookTime"),
                         "totalTime": r.get("totalTime"), "baseServings": r.get("baseServings", 2)}
                        for i, r in enumerate(recipes)],
        }

    # ---- Pinterest ----------------------------------------------------------
    if is_pinterest_url(url):
        source_url = await get_pinterest_source_url(url)
        if source_url:
            url = source_url  # fall through to web path

    # ---- Standard web recipe ------------------------------------------------
    html: Optional[str] = None
    used_jina = False
    try:
        async with httpx.AsyncClient(
            follow_redirects=True, timeout=20.0,
            headers={
                "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.9",
            },
        ) as client:
            resp = await client.get(url)
            if resp.status_code in (402, 403, 401, 429):
                raise httpx.HTTPStatusError("blocked", request=resp.request, response=resp)
            resp.raise_for_status()
            html = resp.text
    except (httpx.HTTPStatusError, httpx.RequestError):
        # Site blocks scrapers — try Jina AI Reader (free, bypasses anti-bot)
        try:
            import urllib.parse as _up
            async with httpx.AsyncClient(timeout=30.0, headers={"Accept": "application/json"}) as jclient:
                jresp = await jclient.get(f"https://r.jina.ai/{_up.quote(url, safe=':/?=&#')}")
                jdata = jresp.json()
                jcontent = jdata.get("data", {}).get("content") or ""
                if len(jcontent) > 500:
                    html = f"<html><body>{jcontent}</body></html>"
                    used_jina = True
        except Exception as je:
            print(f"[Dishpad] Jina fallback failed: {je}")
    if html is None:
        return {"error": "Could not reach that URL. Please check it and try again."}

    jsonld_recipe = extract_jsonld_recipe(html)
    if jsonld_recipe:
        result = jsonld_to_clipresult(jsonld_recipe)
        if result.get("ingredients") and result.get("steps"):
            image_url = result.get("imageUrl") or get_image_url(html, url)
            return {"title": result["title"], "source": url, "imageUrl": image_url,
                    "ingredients": result["ingredients"], "steps": result["steps"],
                    "prepTime": result.get("prepTime"), "cookTime": result.get("cookTime"),
                    "totalTime": result.get("totalTime"), "baseServings": result.get("baseServings", 4)}

    image_url = get_image_url(html, url)
    page_text = extract_page_text(html)
    jsonld_hint = json.dumps(jsonld_recipe, indent=2) if jsonld_recipe else None
    recipe_data = None

    try:
        recipe_data = extract_with_claude(page_text, url, jsonld_hint=jsonld_hint)
    except Exception as e:
        print(f"[Dishpad] Claude web extraction failed: {e}")

    if recipe_data is None:
        try:
            recipe_data = extract_with_scrapers(html, url)
        except Exception:
            return {"error": "No recipe found on that page. Try a different URL or add it manually."}

    if not recipe_data.get("ingredients") and not recipe_data.get("steps"):
        return {"error": "No recipe found on that page. Try a different URL or add it manually."}

    return {
        "title": recipe_data.get("title", "Untitled Recipe"),
        "source": url,
        "imageUrl": image_url or recipe_data.get("imageUrl"),
        "ingredients": recipe_data.get("ingredients", []),
        "steps": recipe_data.get("steps", []),
        "prepTime": recipe_data.get("prepTime"),
        "cookTime": recipe_data.get("cookTime"),
        "totalTime": recipe_data.get("totalTime"),
        "baseServings": recipe_data.get("baseServings", 4),
    }


# ---------------------------------------------------------------------------
# /api/scan
# ---------------------------------------------------------------------------

@app.post("/api/scan")
@limiter.limit("10/minute")
async def scan_recipe(request: Request, body: ScanRequest):
    if not body.image:
        return {"error": "No image provided."}

    client_ip = get_client_ip(request)
    if not is_email_pro(body.proEmail or ""):
        if not check_and_increment_free_usage(client_ip):
            return {"error": (
                f"You've used your {FREE_CLIPS_PER_DAY} free recipe clips. "
                "Upgrade to Dishpad Pro for unlimited clipping."
            )}

    media_type = body.mediaType.lower().split(";")[0].strip()
    if media_type not in SUPPORTED_MEDIA_TYPES:
        return {"error": f"Unsupported image format '{media_type}'. Please use JPEG, PNG, or WebP."}

    if not os.environ.get("ANTHROPIC_API_KEY"):
        return {"error": "Recipe AI is not configured. Please try again later."}

    if len(body.image) > 14_000_000:
        return {"error": "Image is too large. Please use a photo under 10MB."}

    try:
        recipe_data = extract_photo_with_claude(body.image, media_type)
    except Exception as e:
        print(f"[Dishpad] Photo extraction failed: {e}")
        return {"error": "Couldn't extract a recipe from that photo. Make sure the recipe text is clearly visible."}

    if not recipe_data.get("ingredients") and not recipe_data.get("steps"):
        return {"error": "No recipe was found in that photo. Make sure the full recipe is visible and the image is in focus."}

    return {
        "title": recipe_data.get("title", "Scanned Recipe"),
        "source": "Scanned from photo",
        "imageUrl": None,
        "ingredients": recipe_data.get("ingredients", []),
        "steps": recipe_data.get("steps", []),
        "prepTime": recipe_data.get("prepTime"),
        "cookTime": recipe_data.get("cookTime"),
        "totalTime": recipe_data.get("totalTime"),
        "baseServings": recipe_data.get("baseServings", 4),
    }


@app.get("/admin/api/debug/youtube")
async def debug_youtube(url: str, x_admin_password: Optional[str] = Header(None)):
    require_admin(x_admin_password)
    video_id = extract_youtube_video_id(url)
    if not video_id:
        return {"error": "Not a YouTube URL"}
    transcript_result, metadata_result = await asyncio.gather(
        fetch_youtube_transcript(video_id),
        fetch_youtube_metadata(url),
        return_exceptions=True,
    )
    if isinstance(transcript_result, Exception): transcript_result = None
    if isinstance(metadata_result, Exception): metadata_result = {}
    # Also test direct page scraping via mobile URL
    page_title = None
    page_desc = None
    page_debug = []
    for _test_url, _ua in [
        (f"https://m.youtube.com/watch?v={video_id}", "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0) AppleWebKit/605.1.15 Mobile/15E148 Safari/604.1"),
        (url, "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124.0.0.0 Safari/537.36"),
    ]:
        try:
            async with httpx.AsyncClient(follow_redirects=True, timeout=15.0, headers={
                "User-Agent": _ua, "Accept-Language": "en-US,en;q=0.9",
            }) as hc:
                resp = await hc.get(_test_url)
                raw_html = resp.text
                has_ipr = "ytInitialPlayerResponse" in raw_html
                has_og_desc = "og:description" in raw_html
                pi = get_youtube_page_info(raw_html)
                page_debug.append({
                    "url": _test_url[:50], "status": resp.status_code,
                    "html_chars": len(raw_html), "has_ytInitialPlayerResponse": has_ipr,
                    "has_og_description": has_og_desc, "html_snippet": raw_html[:200],
                    "parsed_title": pi.get("title"), "parsed_desc": (pi.get("description") or "")[:100],
                })
                page_title = page_title or pi.get("title")
                page_desc = page_desc or pi.get("description")
            if page_title and page_desc:
                break
        except Exception as e:
            page_debug.append({"url": _test_url[:50], "error": str(e)[:100]})
    # Test oEmbed
    oembed_title = None
    try:
        import urllib.parse
        async with httpx.AsyncClient(timeout=10.0) as hc:
            oe = await hc.get(f"https://www.youtube.com/oembed?url={urllib.parse.quote(url)}&format=json")
            oembed_title = oe.json().get("title")
    except Exception as e:
        oembed_title = f"FAILED: {e}"
    # Test YouTube Data API v3
    yt_api_result = _fetch_youtube_description_via_api(video_id)
    return {
        "video_id": video_id,
        "youtube_api_key_set": bool(YOUTUBE_API_KEY),
        "youtube_api_title": yt_api_result.get("title"),
        "youtube_api_desc_chars": len(yt_api_result.get("description") or ""),
        "youtube_api_desc_sample": (yt_api_result.get("description") or "")[:200],
        "transcript_chars": len(transcript_result) if transcript_result else 0,
        "yt_dlp_title": metadata_result.get("title") if isinstance(metadata_result, dict) else None,
        "page_scrape_title": page_title,
        "page_scrape_desc_chars": len(page_desc or ""),
        "oembed_title": oembed_title,
        "page_debug": page_debug,
    }
