"""
TerraTrace — Environmental Compliance Evidence Management System (local MVP)
Tracks obligations, permits, monitoring results, corrective actions and evidence
by site and reporting period. Deterministic rule engine + full audit trail.
Ships with clearly-labelled SYNTHETIC demo data and a live monitoring simulation.
Decision support only — not a regulatory compliance determination.

Run (Windows PowerShell):
    python -m venv .venv
    .\\.venv\\Scripts\\Activate.ps1
    pip install -r requirements.txt
    streamlit run app.py
"""

import io
import json
import math
import random
import shutil
import sqlite3
import hashlib
import logging
import zipfile
from pathlib import Path
from datetime import date, datetime, timedelta
from contextlib import closing
from html import escape as esc
from urllib.parse import quote

import numpy as np
import pandas as pd
import plotly.graph_objects as go
import plotly.express as px
import streamlit as st
import streamlit.components.v1 as components

# ============================================================ constants
APP_NAME = "TerraTrace"
TAGLINE = "Environmental Compliance Evidence Management"
RULE_VERSION = "R-2026.11"
EF_VERSION = "EF-2026.1 (illustrative)"
SCHEMA_VERSION = 1
BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "terratrace_demo.db"
EVIDENCE_DIR = BASE_DIR / "evidence_store"
TODAY = date.today()
NOW = datetime.now()

def period_of(d):
    return f"{d.year}-Q{(d.month - 1) // 3 + 1}"

CUR_PERIOD = period_of(TODAY)
_q = (TODAY.month - 1) // 3 + 1
PREV_PERIOD = f"{TODAY.year - 1}-Q4" if _q == 1 else f"{TODAY.year}-Q{_q - 1}"
MONTH_END = (TODAY.replace(day=1) + timedelta(days=32)).replace(day=1) - timedelta(days=1)

P = {"bg": "#0B1512", "surf": "#12241D", "over": "#183028", "line": "#1E3A2F",
     "text": "#E8F5EE", "mut": "#8FA89B", "grn": "#2DD4A7", "sky": "#38BDF8",
     "amb": "#F5B84A", "red": "#FB7185", "vio": "#C084FC", "lime": "#A3E635",
     "cyn": "#22D3EE", "org": "#FB923C"}
CH = [P["grn"], P["sky"], P["amb"], P["vio"], P["lime"], P["red"], P["cyn"], P["org"]]

PARAMS = {
    "PH":      {"name": "pH",                    "unit": "pH",    "cat": "Water", "min": 0,   "max": 14,   "lt": "range", "hi": 9.0,  "lo": 6.0, "base": 7.3,  "vol": 0.07},
    "COD":     {"name": "COD",                   "unit": "mg/L",  "cat": "Water", "min": 0,   "max": 2000, "lt": "max",   "hi": 125,  "lo": None,"base": 78,   "vol": 6.0},
    "TSS":     {"name": "Total Suspended Solids","unit": "mg/L",  "cat": "Water", "min": 0,   "max": 500,  "lt": "max",   "hi": 30,   "lo": None,"base": 17,   "vol": 2.4},
    "NH3N":    {"name": "Ammonia-Nitrogen",      "unit": "mg/L",  "cat": "Water", "min": 0,   "max": 100,  "lt": "max",   "hi": 5,    "lo": None,"base": 2.1,  "vol": 0.3},
    "FLOW":    {"name": "Effluent Flow",         "unit": "m³/d",  "cat": "Water", "min": 0,   "max": 30000,"lt": "max",   "hi": 9500, "lo": None,"base": 6200, "vol": 210},
    "TURB":    {"name": "Turbidity",             "unit": "NTU",   "cat": "Water", "min": 0,   "max": 200,  "lt": "max",   "hi": 10,   "lo": None,"base": 4.2,  "vol": 0.55},
    "NOX":     {"name": "NOx (stack)",           "unit": "mg/m³", "cat": "Air",   "min": 0,   "max": 1000, "lt": "max",   "hi": 200,  "lo": None,"base": 142,  "vol": 8.5},
    "SO2":     {"name": "SO2 (stack)",           "unit": "mg/m³", "cat": "Air",   "min": 0,   "max": 1500, "lt": "max",   "hi": 350,  "lo": None,"base": 210,  "vol": 13},
    "PM":      {"name": "Particulate Matter",    "unit": "mg/m³", "cat": "Air",   "min": 0,   "max": 300,  "lt": "max",   "hi": 30,   "lo": None,"base": 16,   "vol": 1.5},
    "LCH_COD": {"name": "Leachate COD",          "unit": "mg/L",  "cat": "Waste", "min": 0,   "max": 3000, "lt": "max",   "hi": 200,  "lo": None,"base": 118,  "vol": 9},
    "CH4":     {"name": "Perimeter Methane",     "unit": "%vol",  "cat": "Waste", "min": 0,   "max": 100,  "lt": "max",   "hi": 5,    "lo": None,"base": 1.8,  "vol": 0.2},
    "NOISE":   {"name": "Boundary Noise",        "unit": "dB(A)", "cat": "Noise", "min": 20,  "max": 120,  "lt": "max",   "hi": 65,   "lo": None,"base": 57,   "vol": 1.4},
}
SITE_META = [
    ("RVB", "Riverbend Water Reclamation Facility", "Municipal wastewater", "State EPA — Region 4", 39.10, -84.51, ["PH", "COD", "TSS", "NH3N", "FLOW", "TURB"]),
    ("HBR", "Harborview Combined Utility",          "Utility (power + water)", "Coastal Air District — Region 9", 33.74, -118.27, ["NOX", "SO2", "PM", "NOISE"]),
    ("NFD", "Northfield Manufacturing Campus",      "Metal finishing manufacturer", "State EPA — Region 2", 42.36, -71.06, ["PH", "COD", "TSS", "NOISE"]),
    ("GLN", "Glenmore Municipal Landfill",          "Municipal solid waste", "State EPA — Region 7", 41.66, -93.62, ["LCH_COD", "CH4", "NOISE"]),
]
SITE_CODES = [s[0] for s in SITE_META]
SITE_NAME = {s[0]: s[1] for s in SITE_META}
SIM_POINTS = {s[0]: s[6] for s in SITE_META}
FREQ = {"PH": "Daily", "COD": "Daily", "TSS": "Daily", "FLOW": "Daily", "TURB": "Daily",
        "NOX": "Daily", "SO2": "Daily", "PM": "Daily", "NH3N": "Weekly",
        "LCH_COD": "Weekly", "CH4": "Weekly", "NOISE": "Weekly"}
USERS = ["A. Rivera", "S. Chen", "M. Okafor", "L. Fontaine"]
ACTORS = {"Administrator": "A. Rivera", "Analyst": "S. Chen", "Reviewer": "M. Okafor", "Stakeholder": "L. Fontaine"}
PERMS = {
    "Administrator": {"create", "edit", "import", "submit", "approve", "reject", "override", "delete", "verify", "admin", "share", "export"},
    "Analyst":       {"create", "edit", "import", "submit", "delete", "share", "export"},
    "Reviewer":      {"approve", "reject", "override", "verify", "share", "export"},
    "Stakeholder":   {"share", "export"},
}
UNC = {"Lab": 0.05, "Sensor": 0.10, "Manual": 0.15, "Simulator": 0.12}
MON_FLOW = ["Draft", "Validated", "Under Review", "Approved", "Rejected", "Archived"]
ACT_FLOW = ["Open", "In Progress", "Blocked", "Resolved", "Verified"]
STATUS_KIND = {"Approved": "ok", "compliant": "ok", "Compliant": "ok", "Active": "ok", "Resolved": "ok",
               "Verified": "ok", "Submitted": "ok", "Done": "ok", "Validated": "info", "In Progress": "info",
               "Under Review": "vio", "warning": "warn", "Open": "warn", "Renewal due": "warn", "late": "warn",
               "exceedance": "bad", "Exceedance": "bad", "Rejected": "bad", "Blocked": "bad",
               "Draft": "mut", "Archived": "mut", "missing": "mut"}
FLAG_EMOJI = {"exceedance": "🔴", "warning": "🟠", "late": "🕒", "missing": "⚪", "out_of_range": "🚫"}
NAV = ["Live Operations", "Obligations & Permits", "Monitoring Register", "Corrective Actions",
       "Evidence Vault", "Import Studio", "Review & Approvals", "Reports & Share", "Audit Trail", "Setup & Docs"]
NAV_ICON = {"Live Operations": "📡", "Obligations & Permits": "📜", "Monitoring Register": "🧪",
            "Corrective Actions": "🛠️", "Evidence Vault": "🗄️", "Import Studio": "📥",
            "Review & Approvals": "✅", "Reports & Share": "📤", "Audit Trail": "🧾", "Setup & Docs": "📋"}
REQ_TEXT = "streamlit\npandas\nnumpy\nplotly\nopenpyxl\n"

SCENARIOS = {
    "Normal operations": {},
    "Storm surge": {"FLOW": 1.40, "TSS": 2.30, "COD": 1.55, "TURB": 2.60, "PH": 0.93, "LCH_COD": 1.50, "CH4": 1.4},
    "Treatment upset": {"COD": 1.95, "NH3N": 2.50, "PH": 0.80, "NOX": 1.30, "LCH_COD": 1.80},
    "Maintenance window": {"FLOW": 0.55, "COD": 0.80, "TSS": 0.80, "NOX": 0.75, "SO2": 0.70, "PM": 0.70},
}

st.set_page_config(page_title=f"{APP_NAME} — {TAGLINE}", page_icon="🌿", layout="wide", initial_sidebar_state="expanded")

LOG = logging.getLogger("terratrace")
if not LOG.handlers:
    try:
        h = logging.FileHandler(BASE_DIR / "terratrace.log", encoding="utf-8")
        h.setFormatter(logging.Formatter('{"ts":"%(asctime)s","level":"%(levelname)s","msg":"%(message)s"}'))
        LOG.addHandler(h)
        LOG.setLevel(logging.INFO)
    except Exception:
        pass

# ============================================================ CSS
CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=IBM+Plex+Mono:wght@400;500;600&display=swap');
html, body, [class*="st-"], .stMarkdown p { font-family: 'Space Grotesk', ui-sans-serif, system-ui, sans-serif; }
code, pre, .tt-mono { font-family: 'IBM Plex Mono', ui-monospace, monospace !important; }
* { scrollbar-width: thin; scrollbar-color: #1E4A3A #0B1512; }
*::-webkit-scrollbar { width: 10px; height: 10px; }
*::-webkit-scrollbar-track { background: #0B1512; }
*::-webkit-scrollbar-thumb { background: #1E4A3A; border-radius: 8px; border: 2px solid #0B1512; }
*::-webkit-scrollbar-thumb:hover { background: #2DD4A7; }
[data-testid="stAppViewContainer"] {
  background: radial-gradient(1100px 750px at 88% -10%, rgba(45,212,167,.10), transparent 60%),
              radial-gradient(900px 700px at -10% 110%, rgba(56,189,248,.08), transparent 55%),
              linear-gradient(160deg,#0B1512 0%,#0D1A15 45%,#0A1310 100%);
}
[data-testid="stAppViewContainer"]::before { content:""; position: fixed; inset: 0; pointer-events: none; opacity:.05; z-index:1;
  background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='140' height='140'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='2'/%3E%3C/filter%3E%3Crect width='140' height='140' filter='url(%23n)' opacity='0.55'/%3E%3C/svg%3E"); }
[data-testid="stHeader"] { background: transparent; }
#MainMenu, footer { visibility: hidden; }
.block-container { padding-top: 1.1rem; padding-bottom: 3rem; animation: ttFade .35s ease; }
@keyframes ttFade { from { opacity: 0; transform: translateY(6px);} to { opacity: 1; transform: none;} }
[data-testid="stSidebar"] { background: linear-gradient(180deg,#0E1E18,#0B1712); border-right: 1px solid #1E3A2F; }
.stButton > button, .stDownloadButton > button { background:#12291F; border:1px solid #24513F; color:#D9F2E6;
  border-radius:10px; font-weight:600; transition: all .15s ease; width:100%; }
.stButton > button:hover, .stDownloadButton > button:hover { border-color:#2DD4A7; color:#2DD4A7; transform: translateY(-1px); }
.stButton > button[kind="primary"] { background: linear-gradient(135deg,#0FA37F,#2DD4A7); color:#06231A; border:none; }
.stButton > button[kind="primary"]:hover { filter: brightness(1.1); box-shadow: 0 6px 22px rgba(45,212,167,.28); color:#06231A; }
.stButton > button:disabled { opacity:.4; }
[data-baseweb="tab-list"] { gap: 4px; border-bottom: 1px solid #1E3A2F; }
[data-baseweb="tab"] { color:#8FA89B; font-weight:600; font-size:13px; }
[aria-selected="true"] { color:#2DD4A7 !important; }
[data-baseweb="tab-highlight"] { background-color:#2DD4A7 !important; }
[data-testid="stDataFrame"] { border:1px solid #1E3A2F; border-radius:12px; overflow:hidden; }
[data-testid="stVerticalBlockBorderWrapper"] { background:#10211B; border-color:#1E3A2F !important; border-radius:12px; }
[data-testid="stExpander"] { border:1px solid #1E3A2F; border-radius:12px; background:#0F1D17; }
.stTextInput input, .stTextArea textarea, .stNumberInput input, [data-baseweb="select"] > div {
  background:#0F1F19 !important; border-color:#24513F !important; border-radius:10px !important; color:#E8F5EE !important; }
.stTextInput input:focus, .stTextArea textarea:focus { border-color:#2DD4A7 !important; box-shadow:0 0 0 1px #2DD4A7; }
[data-testid="stSlider"] [role="slider"] { background:#2DD4A7; border-color:#2DD4A7; }
pre, .stCodeBlock { background:#0A120E !important; border:1px solid #1E3A2F; border-radius:12px; }
[data-testid="stDialog"] > div > div { background:#0F1F19; border:1px solid #24513F; border-radius:16px; }
.tt-brand { display:flex; align-items:center; gap:12px; }
.tt-logo { width:40px; height:40px; border-radius:12px; display:flex; align-items:center; justify-content:center;
  font-size:21px; background: linear-gradient(135deg,#0FA37F,#2DD4A7); box-shadow:0 4px 18px rgba(45,212,167,.35); }
.tt-brand-name { font-size:21px; font-weight:700; letter-spacing:.02em; color:#E8F5EE; line-height:1.1; }
.tt-brand-tag { font-size:11px; color:#8FA89B; letter-spacing:.06em; }
.tt-badge { display:inline-flex; align-items:center; gap:6px; padding:2px 10px; border-radius:999px; font-size:10.5px;
  font-weight:700; letter-spacing:.08em; color:#F5B84A; border:1px solid rgba(245,184,74,.45); background:rgba(245,184,74,.08); }
.tt-dot { width:8px; height:8px; border-radius:50%; background:#2DD4A7; display:inline-block; animation: ttPulse 2s infinite; }
@keyframes ttPulse { 0%{box-shadow:0 0 0 0 rgba(45,212,167,.5);} 70%{box-shadow:0 0 0 8px rgba(45,212,167,0);} 100%{box-shadow:0 0 0 0 rgba(45,212,167,0);} }
.tt-ctx { display:flex; flex-wrap:wrap; gap:14px; align-items:center; font-size:12px; color:#8FA89B;
  padding:8px 14px; border:1px solid #1E3A2F; border-radius:10px; background:rgba(16,33,27,.6); margin:10px 0 4px 0; }
.tt-kpis { display:grid; grid-template-columns: repeat(auto-fit,minmax(168px,1fr)); gap:12px; margin:8px 0 14px 0; }
.tt-card { position:relative; background:linear-gradient(165deg,#12241D,#0E1B16); border:1px solid #1E3A2F;
  border-radius:14px; padding:13px 16px 12px 16px; overflow:hidden; animation: ttFade .4s ease; }
.tt-card::after { content:""; position:absolute; top:0; left:0; right:0; height:3px; background:linear-gradient(90deg,#2DD4A7,#38BDF8); }
.tt-card.tt-ok::after { background:linear-gradient(90deg,#0FA37F,#A3E635); }
.tt-card.tt-warn::after { background:linear-gradient(90deg,#B45309,#F5B84A); }
.tt-card.tt-bad::after { background:linear-gradient(90deg,#9F1239,#FB7185); }
.tt-card.tt-info::after { background:linear-gradient(90deg,#0369A1,#38BDF8); }
.tt-card.tt-vio::after { background:linear-gradient(90deg,#7E22CE,#C084FC); }
.tt-k-label { font-size:10.5px; text-transform:uppercase; letter-spacing:.12em; color:#8FA89B; font-weight:600; }
.tt-k-value { font-size:25px; font-weight:700; color:#E8F5EE; margin-top:3px; line-height:1.15; }
.tt-k-sub { font-size:11.5px; color:#8FA89B; margin-top:3px; }
.tt-pill { display:inline-flex; align-items:center; padding:2px 10px; border-radius:999px; font-size:11px; font-weight:700; white-space:nowrap; }
.tt-ok   { background:rgba(52,211,153,.13); color:#34D399; border:1px solid rgba(52,211,153,.35); }
.tt-warn { background:rgba(245,184,74,.12); color:#F5B84A; border:1px solid rgba(245,184,74,.35); }
.tt-bad  { background:rgba(251,113,133,.12); color:#FB7185; border:1px solid rgba(251,113,133,.35); }
.tt-info { background:rgba(56,189,248,.12); color:#38BDF8; border:1px solid rgba(56,189,248,.35); }
.tt-vio  { background:rgba(192,132,252,.12); color:#C084FC; border:1px solid rgba(192,132,252,.35); }
.tt-mut  { background:rgba(143,168,155,.10); color:#8FA89B; border:1px solid rgba(143,168,155,.30); }
.tt-h { display:flex; align-items:center; gap:9px; font-size:15px; font-weight:700; color:#E8F5EE; margin:14px 0 8px 0; }
.tt-h::before { content:""; width:5px; height:16px; border-radius:3px; background:linear-gradient(180deg,#2DD4A7,#38BDF8); }
.tt-table { width:100%; border-collapse:collapse; font-size:12.5px; }
.tt-table th { text-align:left; font-size:10.5px; text-transform:uppercase; letter-spacing:.1em; color:#8FA89B;
  padding:7px 10px; border-bottom:1px solid #24513F; }
.tt-table td { padding:7px 10px; border-bottom:1px solid rgba(30,58,47,.55); color:#E8F5EE; }
.tt-table .num { font-family:'IBM Plex Mono',monospace; font-size:12px; }
.tt-feed-item { border-left:3px solid #38BDF8; padding:6px 11px; background:#10201A; border-radius:8px;
  margin:6px 0; font-size:12.5px; color:#D9F2E6; animation: ttFade .3s ease; }
.tt-feed-item.tt-f-bad { border-left-color:#FB7185; }
.tt-feed-item.tt-f-warn { border-left-color:#F5B84A; }
.tt-feed-item.tt-f-ok { border-left-color:#2DD4A7; }
.tt-feed-time { font-family:'IBM Plex Mono',monospace; font-size:10.5px; color:#8FA89B; margin-right:8px; }
.tt-share-row { display:flex; flex-wrap:wrap; gap:10px; margin:8px 0; }
.tt-sbtn { padding:10px 16px; border-radius:10px; font-weight:700; font-size:13px; color:#fff !important;
  text-decoration:none !important; display:inline-flex; gap:8px; align-items:center; transition:all .15s ease; }
.tt-sbtn:hover { transform:translateY(-2px); filter:brightness(1.12); }
.tt-li { background:#0A66C2; } .tt-x { background:#111; border:1px solid #333; }
.tt-wa { background:#1FA855; } .tt-em { background:#B45309; }
.tt-meter { height:8px; border-radius:6px; background:#1E3A2F; overflow:hidden; min-width:90px; }
.tt-meter > span { display:block; height:100%; border-radius:6px; background:linear-gradient(90deg,#0FA37F,#A3E635); }
.tt-note { font-size:12px; color:#8FA89B; }
.tt-undo { display:flex; align-items:center; gap:10px; padding:9px 14px; border:1px solid rgba(245,184,74,.45);
  background:rgba(245,184,74,.08); border-radius:10px; color:#F5B84A; font-size:13px; font-weight:600; margin-bottom:8px; }
</style>
"""
st.markdown(CSS, unsafe_allow_html=True)

# ============================================================ small helpers
def now_ts():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def fnum(v, nd=1):
    if v is None:
        return "—"
    try:
        if math.isnan(float(v)):
            return "—"
    except (TypeError, ValueError):
        return "—"
    return f"{float(v):,.{nd}f}"

def pill(txt, kind=None):
    k = kind or STATUS_KIND.get(str(txt), "mut")
    return f'<span class="tt-pill tt-{k}">{esc(str(txt))}</span>'

def card(label, value, sub="", tone="info"):
    return (f'<div class="tt-card tt-{tone}"><div class="tt-k-label">{esc(str(label))}</div>'
            f'<div class="tt-k-value">{value}</div><div class="tt-k-sub">{sub}</div></div>')

def kpis(cards):
    st.markdown('<div class="tt-kpis">' + "".join(cards) + "</div>", unsafe_allow_html=True)

def section(title):
    st.markdown(f'<div class="tt-h">{esc(title)}</div>', unsafe_allow_html=True)

def df_show(df, **kw):
    try:
        return st.dataframe(df, width="stretch", **kw)
    except TypeError:
        return st.dataframe(df, use_container_width=True, **kw)

def style_fig(fig, height=300):
    fig.update_layout(height=height, paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(255,255,255,0.02)",
                      font=dict(color=P["text"], family="Space Grotesk", size=12),
                      margin=dict(l=10, r=10, t=30, b=10),
                      legend=dict(bgcolor="rgba(0,0,0,0)"))
    fig.update_xaxes(gridcolor="rgba(143,168,155,.12)", zerolinecolor="rgba(143,168,155,.2)")
    fig.update_yaxes(gridcolor="rgba(143,168,155,.12)", zerolinecolor="rgba(143,168,155,.2)")
    return fig

COPY_TMPL = """
<button id="cpb" style="width:100%;padding:10px 14px;border-radius:10px;border:1px solid #24513F;
 background:#12291F;color:#D9F2E6;font-weight:700;font-size:13px;cursor:pointer;font-family:sans-serif;">
 📋 __LABEL__</button>
<script>
const txt = __PAYLOAD__;
const b = document.getElementById('cpb');
b.addEventListener('click', async () => {
  try { await navigator.clipboard.writeText(txt); b.textContent = '✅ Copied to clipboard'; }
  catch (e) {
    try {
      const ta = document.createElement('textarea'); ta.value = txt; document.body.appendChild(ta);
      ta.select(); document.execCommand('copy'); document.body.removeChild(ta);
      b.textContent = '✅ Copied to clipboard';
    } catch (e2) { b.textContent = '⚠ Use the copy icon on the code block below'; }
  }
  setTimeout(() => { b.innerHTML = '📋 __LABEL__'; }, 2200);
});
</script>
"""

def copy_button(text, label="Copy to clipboard", height=48):
    payload = json.dumps(str(text)).replace("</", "<\\/")
    html = COPY_TMPL.replace("__PAYLOAD__", payload).replace("__LABEL__", label)
    components.html(html, height=height)

def can(perm):
    return perm in PERMS.get(st.session_state.get("role", "Stakeholder"), set())

def actor():
    return ACTORS.get(st.session_state.get("role", "Stakeholder"), "Demo User")

def goto_page(page):
    st.session_state.nav = page

def scope_sites():
    return st.session_state.get("g_sites") or SITE_CODES

def scope_period():
    return st.session_state.get("g_period", CUR_PERIOD)

def site_label(code):
    return f"{code} — {SITE_NAME.get(code, code)}"

# ============================================================ database
def db():
    c = sqlite3.connect(DB_PATH)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA foreign_keys=ON")
    return c

def exec_sql(sql, params=()):
    with closing(db()) as c:
        c.execute(sql, params)
        c.commit()

def query(sql, params=()):
    with closing(db()) as c:
        return [dict(r) for r in c.execute(sql, params).fetchall()]

def next_id(table, prefix, width=4):
    rows = query(f"SELECT id FROM {table} ORDER BY id DESC LIMIT 1")
    n = 0
    if rows:
        try:
            n = int(str(rows[0]["id"]).split("-")[-1])
        except ValueError:
            n = 0
    return f"{prefix}-{n + 1:0{width}d}"

def audit(action, entity, entity_id, detail, who=None, role=None):
    exec_sql("INSERT INTO audit(ts,actor,role,action,entity,entity_id,detail) VALUES(?,?,?,?,?,?,?)",
             (now_ts(), who or actor(), role or st.session_state.get("role", "system"),
              action, entity, str(entity_id), str(detail)[:900]))

SCHEMA = """
CREATE TABLE IF NOT EXISTS sites(code TEXT PRIMARY KEY, name TEXT, site_type TEXT, jurisdiction TEXT,
  region TEXT, lat REAL, lon REAL, created_at TEXT, updated_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS permits(id TEXT PRIMARY KEY, site_code TEXT REFERENCES sites(code), permit_no TEXT,
  title TEXT, regulator TEXT, issued TEXT, expires TEXT, status TEXT, created_at TEXT, updated_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS obligations(id TEXT PRIMARY KEY, site_code TEXT REFERENCES sites(code),
  permit_id TEXT, kind TEXT, code TEXT, title TEXT, parameter TEXT, unit TEXT, limit_type TEXT,
  limit_value REAL, limit_low REAL, frequency TEXT, next_due TEXT, owner TEXT, status TEXT,
  rule_version TEXT, created_at TEXT, updated_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS monitoring(id TEXT PRIMARY KEY, site_code TEXT REFERENCES sites(code),
  obligation_id TEXT, parameter TEXT, value REAL, unit TEXT, measured_at TEXT, period TEXT, method TEXT,
  source TEXT, provenance TEXT, batch_id TEXT, flags TEXT, status TEXT, reviewer TEXT, review_note TEXT,
  override_value REAL, override_reason TEXT, deleted INTEGER DEFAULT 0, created_at TEXT, updated_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS actions(id TEXT PRIMARY KEY, site_code TEXT REFERENCES sites(code), monitoring_id TEXT,
  title TEXT, description TEXT, severity TEXT, priority INTEGER, status TEXT, assignee TEXT, due_date TEXT,
  resolution TEXT, evidence_id TEXT, deleted INTEGER DEFAULT 0, created_at TEXT, updated_at TEXT, resolved_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS evidence(id TEXT PRIMARY KEY, site_code TEXT REFERENCES sites(code), filename TEXT,
  stored_as TEXT, kind TEXT, sha256 TEXT, size_bytes INTEGER, linked_type TEXT, linked_id TEXT, note TEXT,
  uploaded_by TEXT, period TEXT, deleted INTEGER DEFAULT 0, created_at TEXT, schema_version INTEGER);
CREATE TABLE IF NOT EXISTS audit(id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, actor TEXT, role TEXT,
  action TEXT, entity TEXT, entity_id TEXT, detail TEXT);
CREATE TABLE IF NOT EXISTS imports(id TEXT PRIMARY KEY, filename TEXT, sha256 TEXT, stored_as TEXT,
  rows_total INTEGER, rows_ok INTEGER, rows_err INTEGER, rows_dup INTEGER, actor TEXT, ts TEXT, status TEXT);
CREATE TABLE IF NOT EXISTS saved_views(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE, payload TEXT, created_at TEXT);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
"""

SAMPLE_GOOD_ROWS = [
    ["RVB", "COD", 82.4, "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Lab"],
    ["RVB", "TSS", 18.9, "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["RVB", "PH", 7.4, "pH", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["RVB", "FLOW", 6480, "m3/d", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["HBR", "NOX", 151.2, "mg/m3", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["HBR", "SO2", 224.0, "mg/m3", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["HBR", "PM", 28.4, "mg/m3", (TODAY - timedelta(days=2)).isoformat(), "Lab"],
    ["NFD", "COD", 96.1, "mg/L", (TODAY - timedelta(days=2)).isoformat(), "Lab"],
    ["NFD", "TSS", 21.7, "mg/L", (TODAY - timedelta(days=2)).isoformat(), "Lab"],
    ["GLN", "LCH_COD", 132.5, "mg/L", (TODAY - timedelta(days=3)).isoformat(), "Lab"],
    ["GLN", "CH4", 2.1, "%vol", (TODAY - timedelta(days=3)).isoformat(), "Manual"],
    ["NFD", "NOISE", 59.8, "dB(A)", (TODAY - timedelta(days=3)).isoformat(), "Manual"],
]
IMP_COLS = ["site_code", "parameter", "value", "unit", "measured_at", "method"]
SAMPLE_GOOD = pd.DataFrame(SAMPLE_GOOD_ROWS, columns=IMP_COLS).to_csv(index=False)
SAMPLE_BAD = pd.DataFrame([
    ["XYZ", "COD", 80, "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Lab"],
    ["RVB", "COD", "abc", "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Lab"],
    ["RVB", "TSS", "", "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["RVB", "PH", 22, "pH", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["HBR", "NOX", 150, "gallon", (TODAY - timedelta(days=1)).isoformat(), "Sensor"],
    ["HBR", "SO2", 210, "mg/m3", "2026-13-45", "Sensor"],
    ["NFD", "COD", 90, "mg/L", (TODAY + timedelta(days=30)).isoformat(), "Lab"],
    ["NFD", "BOD9", 40, "mg/L", (TODAY - timedelta(days=1)).isoformat(), "Lab"],
    ["GLN", "CH4", 2.0, "%vol", (TODAY - timedelta(days=2)).isoformat(), "Manual"],
    ["GLN", "CH4", 2.0, "%vol", (TODAY - timedelta(days=2)).isoformat(), "Manual"],
    ["RVB", "NH3N", 2.6, "mg/L", (TODAY - timedelta(days=2)).isoformat(), "Lab"],
], columns=IMP_COLS).to_csv(index=False)


def seed(c):
    """Deterministic synthetic dataset — clearly labelled, never real customer data."""
    rng = random.Random(18)
    ts = now_ts()
    for code, name, typ, jur, lat, lon, _pts in SITE_META:
        c.execute("INSERT INTO sites VALUES(?,?,?,?,?,?,?,?,?,?)",
                  (code, name, typ, jur, jur.split("—")[-1].strip(), lat, lon, ts, ts, SCHEMA_VERSION))
    permits = [
        ("PRM-0001", "RVB", "NPDES-OH-4821", "Wastewater discharge permit", "State EPA", -700, 400, "Active"),
        ("PRM-0002", "HBR", "TITLE-V-114-0092", "Title V air operating permit", "Coastal Air District", -1700, 24, "Renewal due"),
        ("PRM-0003", "NFD", "IND-WQ-2210", "Industrial wastewater permit", "State EPA", -460, 260, "Active"),
        ("PRM-0004", "GLN", "SW-LEACH-0771", "Landfill leachate & gas permit", "State EPA", -580, 150, "Active"),
    ]
    site_permit = {p[1]: p[0] for p in permits}
    for pid, sc, no, title, reg, iss, exp, stt in permits:
        c.execute("INSERT INTO permits VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                  (pid, sc, no, title, reg, (TODAY + timedelta(days=iss)).isoformat(),
                   (TODAY + timedelta(days=exp)).isoformat(), stt, ts, ts, SCHEMA_VERSION))
    obls, n = [], 0
    for sc, _n, _t, _j, _la, _lo, pts in SITE_META:
        for pc in pts:
            n += 1
            pd_ = PARAMS[pc]
            hi = 110.0 if (sc == "NFD" and pc == "COD") else float(pd_["hi"])
            obls.append((f"OBL-{n:04d}", sc, site_permit[sc], "monitor", f"{sc}-{pc}-MON",
                         f"{pd_['name']} — {FREQ[pc]} monitoring", pc, pd_["unit"], pd_["lt"], hi,
                         pd_["lo"], FREQ[pc], MONTH_END.isoformat(), "S. Chen", "Open", RULE_VERSION, ts, ts, SCHEMA_VERSION))
    tasks = [
        ("RVB", "Submit Q3 Discharge Monitoring Report", "Quarterly", (MONTH_END - timedelta(days=92) + timedelta(days=15)), "Submitted"),
        ("HBR", "Title V permit renewal application", "Annual", TODAY + timedelta(days=24), "Open"),
        ("NFD", "Quarterly stack emission test", "Quarterly", TODAY + timedelta(days=12), "Open"),
        ("GLN", "Annual leachate characterization report", "Annual", TODAY + timedelta(days=40), "Open"),
        ("NFD", "Sludge waste manifest reconciliation", "Monthly", TODAY - timedelta(days=6), "Open"),
        ("RVB", "Sampler calibration verification", "Monthly", TODAY + timedelta(days=3), "Open"),
    ]
    for sc, title, freq, due, stt in tasks:
        n += 1
        obls.append((f"OBL-{n:04d}", sc, site_permit[sc], "task", f"{sc}-TASK-{n}", title, None, None,
                     None, None, None, freq, due.isoformat(), "S. Chen", stt, RULE_VERSION, ts, ts, SCHEMA_VERSION))
    c.executemany("INSERT INTO obligations VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", obls)
    obl_by_sp = {(o[1], o[6]): o for o in obls if o[3] == "monitor"}

    anom = {("RVB", "COD", 12): 148.2, ("NFD", "TSS", 5): 34.6, ("RVB", "PH", 3): 5.8,
            ("HBR", "NOX", 1): 208.4, ("GLN", "LCH_COD", 9): 214.0,
            ("RVB", "TSS", 7): 28.1, ("HBR", "PM", 2): 28.9, ("NFD", "COD", 4): 104.0}
    mon_rows, anom_ids, k = [], {}, 0
    for o in obls:
        if o[3] != "monitor":
            continue
        sc, pc, unit, lt, hi, lo = o[1], o[6], o[7], o[8], o[9], o[10]
        pdef = PARAMS[pc]
        step = 3 if o[11] == "Daily" else 7
        for age in range(84, -1, -step):
            k += 1
            mid = f"MON-{k:04d}"
            d = TODAY - timedelta(days=age)
            when = datetime(d.year, d.month, d.day, 8 + rng.randint(0, 8), rng.randint(0, 59))
            val = round(pdef["base"] + rng.gauss(0, pdef["vol"] * 0.9), 2)
            val = max(pdef["min"], min(pdef["max"], val))
            if (sc, pc, age) in anom:
                val = anom[(sc, pc, age)]
                anom_ids[(sc, pc)] = mid
            method = "Lab" if step == 7 else ("Sensor" if rng.random() < 0.8 else "Lab")
            if pc == "NOISE":
                method = "Manual"
            flags = classify(val, lt, hi, lo, 0.10)[0]
            flags = "" if flags == "compliant" else flags
            late = (sc == "HBR" and pc == "SO2" and age == 8)
            missing = (sc == "GLN" and pc == "CH4" and age == 2)
            if missing:
                val, flags = None, "missing"
            if late:
                flags = (flags + ",late").strip(",")
            if (sc, pc) in anom_ids and anom_ids[(sc, pc)] == mid and "exceedance" in flags:
                stt, rev, note = "Under Review", "", ""
                if (sc, pc) == ("RVB", "COD"):
                    stt = "Validated"
            elif missing:
                stt, rev, note = "Draft", "", ""
            elif age > 21:
                stt, rev, note = "Approved", "M. Okafor", "Verified against source evidence."
            elif age > 10:
                stt, rev, note = ("Validated" if rng.random() < 0.7 else "Under Review"), "", ""
            else:
                stt, rev, note = ("Draft" if rng.random() < 0.4 else "Validated"), "", ""
            mon_rows.append((mid, sc, o[0], pc, val, unit, when.strftime("%Y-%m-%d %H:%M"), period_of(d),
                             method, "seed", f"seed:synthetic:v1:{o[5]}:age{age}", "SEED-DEMO", flags, stt,
                             rev, note, None, None, 0, ts, ts, SCHEMA_VERSION))
    c.executemany("INSERT INTO monitoring VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", mon_rows)

    acts = [
        ("ACT-0001", "RVB", anom_ids.get(("RVB", "COD")), "Investigate COD exceedance (148 mg/L)",
         "Effluent COD above 125 mg/L permit limit. Check aeration basin DO and influent load; re-sample within 24 h.",
         "High", 1, "In Progress", "S. Chen", TODAY + timedelta(days=2), "", None),
        ("ACT-0002", "NFD", anom_ids.get(("NFD", "TSS")), "Clarifier TSS carryover — line 2",
         "TSS 34.6 mg/L vs 30 mg/L limit. Inspect clarifier weir and sludge withdrawal rate.",
         "High", 2, "Open", "S. Chen", TODAY - timedelta(days=2), "", None),
        ("ACT-0003", "RVB", anom_ids.get(("RVB", "PH")), "Low pH excursion at outfall",
         "pH 5.8 below 6.0 lower bound. Verify neutralization dosing and upstream industrial discharge.",
         "Critical", 3, "Open", "A. Rivera", TODAY + timedelta(days=1), "", None),
        ("ACT-0004", "HBR", anom_ids.get(("HBR", "NOX")), "NOx above hourly ceiling — Unit 3",
         "NOx 208 mg/m³ vs 200 limit. SCR catalyst replacement part on order.",
         "High", 4, "Blocked", "M. Okafor", TODAY + timedelta(days=6), "", None),
        ("ACT-0005", "GLN", anom_ids.get(("GLN", "LCH_COD")), "Leachate COD spike — cell B",
         "Leachate COD 214 mg/L vs 200 limit. Increase recirculation and schedule confirmatory lab sample.",
         "Medium", 5, "In Progress", "S. Chen", TODAY + timedelta(days=4), "", None),
        ("ACT-0006", "RVB", None, "Aerator bearing replacement (completed)",
         "Preventive replacement after vibration alarm; follow-up sampling confirmed normal COD.",
         "Medium", 6, "Verified", "A. Rivera", TODAY - timedelta(days=10),
         "Bearing replaced; 3 consecutive compliant COD results.", None),
    ]
    for aid, sc, mid, title, desc, sev, pri, stt, asg, due, res, ev in acts:
        c.execute("INSERT INTO actions VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                  (aid, sc, mid, title, desc, sev, pri, stt, asg, due.isoformat(), res, ev, 0, ts, ts,
                   ts if stt in ("Resolved", "Verified") else None, SCHEMA_VERSION))

    EVIDENCE_DIR.mkdir(exist_ok=True)
    (EVIDENCE_DIR / "imports").mkdir(exist_ok=True)
    ev_items = [
        ("EVI-0001", "RVB", "Discharge_Permit_NPDES-OH-4821.txt", "Permit", "permit", "PRM-0001",
         f"SYNTHETIC DEMO PERMIT EXTRACT\nPermit: NPDES-OH-4821\nFacility: {SITE_NAME['RVB']}\n"
         f"Effluent limits: COD <= 125 mg/L; TSS <= 30 mg/L; pH 6.0-9.0; Flow <= 9500 m3/d.\n"
         f"Monitoring: daily composite; DMR quarterly.\nIssued {TODAY - timedelta(days=700)}.\nLABEL: SYNTHETIC — NOT A REAL PERMIT."),
        ("EVI-0002", "HBR", "TitleV_Permit_114-0092_Renewal.txt", "Permit", "permit", "PRM-0002",
         f"SYNTHETIC DEMO PERMIT EXTRACT\nPermit: TITLE-V-114-0092\nFacility: {SITE_NAME['HBR']}\n"
         f"Limits: NOx <= 200 mg/m3; SO2 <= 350 mg/m3; PM <= 30 mg/m3.\nExpires {TODAY + timedelta(days=24)} — renewal application required.\nLABEL: SYNTHETIC."),
        ("EVI-0003", "RVB", f"Lab_Certificate_COD_{anom_ids.get(('RVB','COD'),'MON')}.txt", "Lab Certificate", "monitoring",
         anom_ids.get(("RVB", "COD"), ""),
         f"SYNTHETIC LAB CERTIFICATE — DEMO\nAccredited lab: River Analytics (fictional)\nSample: 24h composite effluent\n"
         f"COD: 148.2 mg/L (method SM 5220 D, uncertainty ±5%)\nExceeds permit limit 125 mg/L.\nAnalyst: J. Park (synthetic)\nLinked record: {anom_ids.get(('RVB','COD'),'')}"),
        ("EVI-0004", "NFD", "Stack_Test_Q3_Summary.txt", "Lab Certificate", "site", "NFD",
         "SYNTHETIC STACK TEST SUMMARY — DEMO\nNOx avg 149 mg/m3, SO2 avg 215 mg/m3, PM avg 17 mg/m3.\nAll within permit limits during test window.\nLABEL: SYNTHETIC."),
        ("EVI-0005", "RVB", "Sampler_Calibration_Log.txt", "Calibration", "obligation", "OBL-0006",
         "SYNTHETIC CALIBRATION LOG — DEMO\nAutosampler AS-220: pH buffer 7.00 verified ±0.02; flow meter K-factor confirmed.\nNext verification due in 3 days."),
        ("EVI-0006", "RVB", "DMR_Q3_Submission_Receipt.txt", "Submission", "obligation", None,
         f"SYNTHETIC SUBMISSION RECEIPT — DEMO\nQ3 Discharge Monitoring Report submitted {TODAY - timedelta(days=60)}.\nAcknowledgement ID: DMR-DEMO-3Q.\nLABEL: SYNTHETIC."),
        ("EVI-0007", "RVB", "Aerator_Work_Order_Closeout.txt", "Maintenance", "action", "ACT-0006",
         "SYNTHETIC WORK ORDER — DEMO\nWO-4471: Aerator #2 bearing replaced.\nPost-work COD: 79 / 81 / 77 mg/L (compliant).\nVerified by M. Okafor."),
    ]
    for eid, sc, fname, kind, ltype, lid, content in ev_items:
        if ltype == "obligation" and lid is None:
            lid = next((o[0] for o in obls if o[3] == "task" and "Discharge Monitoring" in o[5]), "")
        data = content.encode("utf-8")
        stored = f"{eid}_{fname}"
        (EVIDENCE_DIR / stored).write_bytes(data)
        c.execute("INSERT INTO evidence VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                  (eid, sc, fname, stored, kind, hashlib.sha256(data).hexdigest(), len(data), ltype, lid,
                   "Seeded synthetic evidence", "A. Rivera", CUR_PERIOD, 0, ts, SCHEMA_VERSION))
    c.execute("UPDATE actions SET evidence_id='EVI-0007' WHERE id='ACT-0006'")
    hist = (EVIDENCE_DIR / "imports" / "IMP-0001_historical_import_q3.csv")
    hist.write_text(SAMPLE_GOOD, encoding="utf-8")
    c.execute("INSERT INTO imports VALUES(?,?,?,?,?,?,?,?,?,?,?)",
              ("IMP-0001", "historical_import_q3.csv", hashlib.sha256(SAMPLE_GOOD.encode()).hexdigest(),
               "imports/IMP-0001_historical_import_q3.csv", 12, 12, 0, 0, "S. Chen", ts, "committed (seed)"))
    c.executemany("INSERT INTO audit(ts,actor,role,action,entity,entity_id,detail) VALUES(?,?,?,?,?,?,?)", [
        (ts, "System", "system", "seed", "database", "demo", "Synthetic dataset v1 generated (deterministic seed 18). All data labelled SYNTHETIC."),
        (ts, "M. Okafor", "Reviewer", "approve", "monitoring", "bulk-seed", "Historical readings older than 21 days approved against source evidence."),
        (ts, "S. Chen", "Analyst", "import", "imports", "IMP-0001", "Historical Q3 import committed: 12 ok / 0 errors / 0 duplicates."),
    ])
    c.execute("INSERT INTO saved_views(name,payload,created_at) VALUES(?,?,?)",
              ("⚠ Exceedances in review", json.dumps({"status": ["Under Review", "Validated"], "flags": ["exceedance"],
               "sites": SITE_CODES, "method": [], "search": "", "sort": "Newest first"}), ts))
    for k_, v_ in [("rule_version", RULE_VERSION), ("ef_version", EF_VERSION), ("warn_margin", "0.10"),
                   ("retention_days", "2555"), ("auto_log", "1")]:
        c.execute("INSERT OR REPLACE INTO settings VALUES(?,?)", (k_, v_))


def init_db():
    fresh = not DB_PATH.exists()
    with closing(db()) as c:
        c.executescript(SCHEMA)
        c.commit()
        if c.execute("SELECT COUNT(*) FROM sites").fetchone()[0] == 0:
            seed(c)
            c.commit()
            st.session_state.fresh_seed = True
    return fresh

def setting(key, default=""):
    r = query("SELECT value FROM settings WHERE key=?", (key,))
    return r[0]["value"] if r else default

def get_limits():
    rows = query("SELECT * FROM obligations WHERE kind='monitor' AND status!='Archived'")
    return {(r["site_code"], r["parameter"]): r for r in rows}

# ============================================================ domain engine (deterministic, UI-independent)
def classify(value, limit_type, limit_value, limit_low, margin=0.10):
    """Rule R-2026.11 §1: limit classification. Returns (status, headroom_pct, note)."""
    if value is None or (isinstance(value, float) and math.isnan(value)):
        return "missing", None, "No measured value — exception path."
    v = float(value)
    if limit_type == "max":
        lim = float(limit_value)
        head = (lim - v) / lim * 100 if lim else None
        if v > lim:
            return "exceedance", head, f"{v:g} > limit {lim:g}"
        if v > lim * (1 - margin):
            return "warning", head, f"Within {margin:.0%} of limit {lim:g}"
        return "compliant", head, f"{v:g} ≤ limit {lim:g}"
    if limit_type == "min":
        lim = float(limit_value)
        head = (v - lim) / lim * 100 if lim else None
        if v < lim:
            return "exceedance", head, f"{v:g} < minimum {lim:g}"
        if v < lim * (1 + margin):
            return "warning", head, f"Within {margin:.0%} of minimum"
        return "compliant", head, f"{v:g} ≥ minimum {lim:g}"
    lo, hi = float(limit_low), float(limit_value)
    band = (hi - lo) * margin
    if v < lo or v > hi:
        return "exceedance", None, f"{v:g} outside range {lo:g}–{hi:g}"
    if v < lo + band or v > hi - band:
        return "warning", None, f"Near range edge ({lo:g}–{hi:g})"
    return "compliant", None, f"{v:g} within range {lo:g}–{hi:g}"

def plausible(param, value):
    p = PARAMS.get(param)
    if p is None or value is None:
        return False
    return p["min"] <= float(value) <= p["max"]

def mass_load_kg_d(flow_m3d, conc_mg_l):
    """Load (kg/d) = flow (m³/d) × concentration (mg/L) ÷ 1000. Hand-check: 5000×20/1000 = 100."""
    if flow_m3d is None or conc_mg_l is None or float(flow_m3d) < 0 or float(conc_mg_l) < 0:
        raise ValueError("Flow and concentration must be non-negative numbers.")
    return float(flow_m3d) * float(conc_mg_l) / 1000.0

def co2e_tonnes(activity_t, ef_kg_per_t):
    """tCO2e = activity (t) × EF (kg CO2e / t) ÷ 1000. Hand-check: 100×3170/1000 = 317."""
    if activity_t is None or ef_kg_per_t is None or float(activity_t) < 0 or float(ef_kg_per_t) < 0:
        raise ValueError("Activity and emission factor must be non-negative numbers.")
    return float(activity_t) * float(ef_kg_per_t) / 1000.0

def zscore_anomaly(value, history):
    """Baseline heuristic (not ML): |z| > 2.5 vs trailing window flags a statistical anomaly."""
    h = [float(x) for x in history if x is not None]
    if len(h) < 8:
        return None, False
    mu, sd = float(np.mean(h)), float(np.std(h))
    if sd < 1e-9:
        return 0.0, False
    z = (float(value) - mu) / sd
    return z, abs(z) > 2.5

def canon_unit(u):
    s = str(u).strip().lower().replace("³", "3").replace("µ", "u")
    aliases = {"db(a)": "dB(A)", "dba": "dB(A)", "%": "%vol", "percent": "%vol", "m3/day": "m³/d", "m3/d": "m³/d"}
    if s in aliases:
        return aliases[s]
    for p in PARAMS.values():
        if s == p["unit"].lower().replace("³", "3"):
            return p["unit"]
    return str(u).strip()

def limit_str(obl):
    if obl is None:
        return "—"
    if obl["limit_type"] == "range":
        return f"{fnum(obl['limit_low'], 1)}–{fnum(obl['limit_value'], 1)}"
    sym = "≤" if obl["limit_type"] == "max" else "≥"
    return f"{sym} {fnum(obl['limit_value'], 1)}"

def effective_value(rec):
    return rec["override_value"] if rec.get("override_value") is not None else rec.get("value")

def explain_record(rec, obl):
    """Structured explanation: inputs, rule version, uncertainty, warnings, reviewer status."""
    eff = effective_value(rec)
    method = rec.get("method", "Manual")
    u_pct = UNC.get(method, 0.15)
    status, head, note = classify(eff, obl["limit_type"], obl["limit_value"], obl["limit_low"],
                                  float(setting("warn_margin", "0.10"))) if obl else ("missing", None, "No linked obligation")
    borderline = False
    if eff is not None and obl:
        u = abs(float(eff)) * u_pct
        if obl["limit_type"] == "max" and status != "exceedance":
            borderline = float(eff) + u > float(obl["limit_value"])
        elif obl["limit_type"] == "range" and status != "exceedance":
            borderline = float(eff) - u < float(obl["limit_low"]) or float(eff) + u > float(obl["limit_value"])
    warnings = []
    for f in (rec.get("flags") or "").split(","):
        if f == "late":
            warnings.append("Sample collected after its scheduled window (late).")
        if f == "missing":
            warnings.append("Missing measured value — cannot validate; exception path.")
        if f == "exceedance":
            warnings.append("Permit-limit exceedance — corrective action + human review required.")
    if borderline:
        warnings.append(f"Borderline: within ±{u_pct:.0%} measurement uncertainty of the limit — confirm with a lab sample.")
    if rec.get("override_value") is not None:
        warnings.append(f"Manual override applied: {rec.get('override_reason','')} (original value preserved).")
    return {"effective": eff, "uncertainty_pct": u_pct, "status": status, "headroom": head, "note": note,
            "borderline": borderline, "warnings": warnings, "rule_version": RULE_VERSION}

# ============================================================ services
def flags_for(site, param, value, late=False):
    obl = get_limits().get((site, param))
    if value is None:
        return "missing"
    stt = classify(value, obl["limit_type"], obl["limit_value"], obl["limit_low"],
                   float(setting("warn_margin", "0.10")))[0] if obl else "compliant"
    fl = "" if stt == "compliant" else stt
    if late:
        fl = (fl + ",late").strip(",")
    return fl

def insert_monitoring(site, param, value, unit, measured_at, method, source, provenance, batch, status="Draft", late=False):
    mid = next_id("monitoring", "MON")
    obl = get_limits().get((site, param))
    d = pd.to_datetime(measured_at).date()
    exec_sql("INSERT INTO monitoring VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
             (mid, site, obl["id"] if obl else None, param, None if value is None else float(value), unit,
              str(measured_at), period_of(d), method, source, provenance, batch,
              flags_for(site, param, value, late), status, "", "", None, None, 0, now_ts(), now_ts(), SCHEMA_VERSION))
    return mid

def transition(ids, target, note=""):
    """Lifecycle transitions with server-side role + domain guards. Returns (done, skipped msgs)."""
    done, skipped = [], []
    role = st.session_state.get("role", "Stakeholder")
    for mid in ids:
        r = query("SELECT * FROM monitoring WHERE id=? AND deleted=0", (mid,))
        if not r:
            skipped.append(f"{mid}: not found")
            continue
        r = r[0]
        cur = r["status"]
        ok, why = False, ""
        if target == "Validated":
            ok = can("submit") and cur == "Draft"
            why = "needs Draft + Analyst role"
            if ok and r["value"] is None:
                ok, why = False, "missing value — stays Draft (exception)"
        elif target == "Under Review":
            ok = can("submit") and cur in ("Draft", "Validated")
            why = "needs Draft/Validated + Analyst role"
            if ok and r["value"] is None:
                ok, why = False, "missing value — cannot submit"
        elif target == "Approved":
            ok = can("approve") and cur in ("Validated", "Under Review")
            why = "needs Validated/Under Review + Reviewer role"
            if ok and "exceedance" in (r["flags"] or ""):
                linked = query("SELECT id FROM actions WHERE monitoring_id=? AND deleted=0", (mid,))
                if not linked and len(note.strip()) < 5:
                    ok, why = False, "exceedance approval needs a corrective action or a review note ≥ 5 chars"
        elif target == "Rejected":
            ok = can("reject") and cur in ("Validated", "Under Review") and len(note.strip()) >= 5
            why = "needs Reviewer role + rejection reason ≥ 5 chars"
        elif target == "Draft":
            ok = can("edit") and cur in ("Rejected", "Validated", "Under Review")
            why = "needs Analyst role + review-stage record"
        elif target == "Archived":
            ok = can("admin") and cur in ("Approved", "Rejected")
            why = "needs Administrator + decided record"
        if ok:
            rev = actor() if target in ("Approved", "Rejected") else r["reviewer"]
            exec_sql("UPDATE monitoring SET status=?, reviewer=?, review_note=?, updated_at=? WHERE id=?",
                     (target, rev, note or r["review_note"], now_ts(), mid))
            audit(f"status:{target}", "monitoring", mid, f"{cur} → {target}. {note}".strip())
            done.append(mid)
        else:
            skipped.append(f"{mid}: {why}")
    return done, skipped

def soft_delete(table, rid):
    if not can("delete"):
        return False
    exec_sql(f"UPDATE {table} SET deleted=1 WHERE id=?", (rid,))
    audit("delete", table, rid, "Soft-deleted (undo available).")
    st.session_state.undo = {"table": table, "id": rid}
    return True

def undo_delete():
    u = st.session_state.pop("undo", None)
    if u:
        exec_sql(f"UPDATE {u['table']} SET deleted=0 WHERE id=?", (u["id"],))
        audit("undo_delete", u["table"], u["id"], "Deletion undone.")
        return u["id"]
    return None

def save_evidence(site, filename, data, kind, linked_type, linked_id, note):
    if len(data) > 25 * 1024 * 1024:
        raise ValueError("File exceeds the 25 MB upload cap.")
    eid = next_id("evidence", "EVI")
    safe = "".join(ch for ch in filename if ch.isalnum() or ch in "._- ")[:80] or "file.bin"
    stored = f"{eid}_{safe}"
    EVIDENCE_DIR.mkdir(exist_ok=True)
    (EVIDENCE_DIR / stored).write_bytes(data)
    exec_sql("INSERT INTO evidence VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
             (eid, site, filename, stored, kind, hashlib.sha256(data).hexdigest(), len(data),
              linked_type, linked_id, note, actor(), CUR_PERIOD, 0, now_ts(), SCHEMA_VERSION))
    audit("upload", "evidence", eid, f"{filename} ({len(data)} bytes) sha256 recorded.")
    return eid

def validate_import(df, filename):
    """Row-level validation with actionable errors. Never mutates the DB."""
    missing_cols = [c for c in IMP_COLS if c not in df.columns]
    if missing_cols:
        return {"fatal": f"Missing required columns: {', '.join(missing_cols)}. Expected: {', '.join(IMP_COLS)}"}
    limits = get_limits()
    seen, preview, valid, errors = set(), [], [], []
    n_ok = n_err = n_dup = 0
    for i, row in df.iterrows():
        rownum = int(i) + 2
        errs = []
        site = str(row.get("site_code", "")).strip().upper()
        param = str(row.get("parameter", "")).strip().upper()
        unit = canon_unit(row.get("unit", ""))
        method = str(row.get("method", "")).strip().title()
        raw_val = row.get("value", None)
        raw_date = row.get("measured_at", None)
        val = None
        try:
            if raw_val is None or str(raw_val).strip() == "" or str(raw_val).lower() == "nan":
                errs.append("value is missing — numeric required (log exceptions via Quick entry)")
            else:
                val = float(raw_val)
        except (TypeError, ValueError):
            errs.append(f"value '{raw_val}' is not numeric")
        d = pd.to_datetime(raw_date, errors="coerce")
        if site not in SITE_CODES:
            errs.append(f"unknown site_code '{site}' — valid: {', '.join(SITE_CODES)}")
        if param not in PARAMS:
            errs.append(f"unknown parameter '{param}' — see catalog in Setup & Docs")
        else:
            if unit != PARAMS[param]["unit"]:
                errs.append(f"unit '{row.get('unit','')}' ≠ expected '{PARAMS[param]['unit']}' for {param}")
            if val is not None and not plausible(param, val):
                errs.append(f"{param} {val:g} outside plausible {PARAMS[param]['min']}–{PARAMS[param]['max']} — check instrument/unit")
            if site in SITE_CODES and (site, param) not in limits:
                errs.append(f"no monitoring obligation for {site}/{param} — create it first (referential integrity)")
        if pd.isna(d):
            errs.append(f"measured_at '{raw_date}' is not a date — use YYYY-MM-DD")
        elif d.date() > TODAY:
            errs.append("measured_at is in the future")
        if method not in ("Lab", "Sensor", "Manual"):
            errs.append(f"method '{row.get('method','')}' invalid — use Lab, Sensor or Manual")
        dup = False
        if not errs:
            key = (site, param, d.strftime("%Y-%m-%d %H:%M"))
            exists = query("SELECT 1 FROM monitoring WHERE site_code=? AND parameter=? AND measured_at=? AND deleted=0", key)
            if key in seen or exists:
                dup = True
            seen.add(key)
        status = "ERROR" if errs else ("DUPLICATE" if dup else "OK")
        if errs:
            n_err += 1
            errors.append({"row": rownum, "site_code": site, "parameter": param, "errors": "; ".join(errs)})
        elif dup:
            n_dup += 1
        else:
            n_ok += 1
            valid.append({"site": site, "param": param, "value": val, "unit": unit,
                          "measured_at": d.strftime("%Y-%m-%d %H:%M"), "method": method, "row": rownum})
        preview.append({"row": rownum, "site_code": site, "parameter": param, "value": raw_val, "unit": unit,
                        "measured_at": str(raw_date), "method": method,
                        "status": {"OK": "🟢 OK", "ERROR": "🔴 ERROR", "DUPLICATE": "🟡 DUPLICATE"}[status],
                        "errors": "; ".join(errs) or ("skipped — key already present (safe re-import)" if dup else "")})
    return {"fatal": None, "preview": pd.DataFrame(preview), "errors": pd.DataFrame(errors),
            "valid": valid, "ok": n_ok, "err": n_err, "dup": n_dup, "total": len(df), "filename": filename}

def commit_import(res, raw_bytes):
    batch = next_id("imports", "IMP")
    safe = "".join(ch for ch in res["filename"] if ch.isalnum() or ch in "._-")[:60] or "upload.csv"
    rel = f"imports/{batch}_{safe}"
    (EVIDENCE_DIR / "imports").mkdir(parents=True, exist_ok=True)
    (EVIDENCE_DIR / rel).write_bytes(raw_bytes)
    for v in res["valid"]:
        insert_monitoring(v["site"], v["param"], v["value"], v["unit"], v["measured_at"], v["method"],
                          "import", f"import:{res['filename']}:row {v['row']}", batch, status="Validated")
    exec_sql("INSERT INTO imports VALUES(?,?,?,?,?,?,?,?,?,?,?)",
             (batch, res["filename"], hashlib.sha256(raw_bytes).hexdigest(), rel, res["total"],
              res["ok"], res["err"], res["dup"], actor(), now_ts(), "committed"))
    audit("import", "imports", batch,
          f"{res['filename']}: {res['ok']} imported / {res['err']} errors / {res['dup']} duplicates skipped. Original preserved.")
    return batch

# ============================================================ reports & sharing
def build_report(period, sites, include_drafts=False):
    where, params = ["deleted=0", "value IS NOT NULL OR flags LIKE '%missing%'"], []
    if sites:
        where.append(f"site_code IN ({','.join('?' * len(sites))})")
        params += list(sites)
    if period != "All periods":
        where.append("period=?")
        params.append(period)
    statuses = MON_FLOW if include_drafts else ["Validated", "Under Review", "Approved", "Rejected"]
    where.append(f"status IN ({','.join('?' * len(statuses))})")
    params += statuses
    rows = query(f"SELECT * FROM monitoring WHERE {' AND '.join(where)} ORDER BY measured_at", params)
    df = pd.DataFrame(rows)
    assessed = df[df["value"].notna()] if len(df) else df
    n_assessed = len(assessed)
    n_exc = int(assessed["flags"].fillna("").str.contains("exceedance").sum()) if n_assessed else 0
    n_warn = int(assessed["flags"].fillna("").str.contains("warning").sum()) if n_assessed else 0
    pct = (n_assessed - n_exc) / n_assessed * 100 if n_assessed else 0.0
    per_site = []
    for sc in sites:
        sub = assessed[assessed["site_code"] == sc] if n_assessed else assessed
        na = len(sub)
        ne = int(sub["flags"].fillna("").str.contains("exceedance").sum()) if na else 0
        per_site.append({"Site": sc, "Name": SITE_NAME[sc], "Assessed": na, "Exceedances": ne,
                         "Compliance %": round((na - ne) / na * 100, 1) if na else 0.0})
    limits = get_limits()
    per_obl = []
    if n_assessed:
        for (sc, pc), sub in assessed.groupby(["site_code", "parameter"]):
            ne = int(sub["flags"].fillna("").str.contains("exceedance").sum())
            obl = limits.get((sc, pc))
            per_obl.append({"Site": sc, "Parameter": PARAMS[pc]["name"], "Unit": PARAMS[pc]["unit"],
                            "Limit": limit_str(obl), "Readings": len(sub), "Exceedances": ne,
                            "Worst": float(sub["value"].max()) if obl and obl["limit_type"] != "min" else float(sub["value"].min()),
                            "Compliance %": round((len(sub) - ne) / len(sub) * 100, 1)})
    exc_rows = df[df["flags"].fillna("").str.contains("exceedance|missing|late") & (df["status"] != "Approved")] if len(df) else df
    acts = query(f"SELECT * FROM actions WHERE deleted=0 AND site_code IN ({','.join('?' * len(sites))}) AND status!='Verified' ORDER BY priority", sites)
    overdue = [a for a in acts if a["due_date"] < TODAY.isoformat() and a["status"] not in ("Resolved", "Verified")]
    ev = query(f"SELECT * FROM evidence WHERE deleted=0 AND site_code IN ({','.join('?' * len(sites))})", sites)
    approvals = df["status"].value_counts().to_dict() if len(df) else {}
    trend = pd.DataFrame()
    if n_assessed:
        t = assessed.copy()
        t["week"] = pd.to_datetime(t["measured_at"]).dt.to_period("W").dt.start_time
        trend = t.groupby("week").apply(
            lambda g: pd.Series({"Compliance %": round((len(g) - g["flags"].fillna("").str.contains("exceedance").sum()) / len(g) * 100, 1),
                                 "Exceedances": int(g["flags"].fillna("").str.contains("exceedance").sum())}),
            include_groups=False).reset_index()
    return {"period": period, "sites": sites, "df": df, "n_assessed": n_assessed, "n_exc": n_exc, "n_warn": n_warn,
            "pct": pct, "per_site": pd.DataFrame(per_site), "per_obl": pd.DataFrame(per_obl),
            "exceptions": exc_rows, "actions": acts, "overdue": overdue, "evidence": ev, "approvals": approvals,
            "trend": trend, "generated": now_ts(), "actor": actor(),
            "versions": {"rules": RULE_VERSION, "factors": EF_VERSION, "schema": SCHEMA_VERSION},
            "drafts": include_drafts}

REPORT_CSS = """
<style>
body{font-family:'Segoe UI',system-ui,sans-serif;background:#F7F5EF;color:#1C2B24;margin:0;padding:34px 44px;}
*{scrollbar-width:thin;scrollbar-color:#0FA37F #EDEAE0;}
*::-webkit-scrollbar{width:10px}*::-webkit-scrollbar-track{background:#EDEAE0}
*::-webkit-scrollbar-thumb{background:#0FA37F;border-radius:8px;border:2px solid #EDEAE0}
h1{font-size:24px;margin:0;color:#0B3D2E}h2{font-size:16px;color:#0B3D2E;border-bottom:2px solid #0FA37F;padding-bottom:5px;margin-top:28px}
.badge{display:inline-block;background:#FFF3D6;color:#8A5A00;border:1px solid #E4C069;border-radius:999px;padding:3px 12px;font-size:11px;font-weight:700;letter-spacing:.06em}
.meta{color:#5B6E64;font-size:12px;margin:8px 0 18px 0}
.kpis{display:flex;gap:14px;flex-wrap:wrap;margin:14px 0}
.k{background:#fff;border:1px solid #DAD6C8;border-radius:12px;padding:12px 18px;min-width:140px;border-top:4px solid #0FA37F}
.k b{display:block;font-size:23px;color:#0B3D2E}.k span{font-size:11px;color:#5B6E64;text-transform:uppercase;letter-spacing:.08em}
table{width:100%;border-collapse:collapse;font-size:12.5px;background:#fff;border:1px solid #DAD6C8;border-radius:8px;overflow:hidden}
th{background:#0B3D2E;color:#EAF7F0;text-align:left;padding:8px 10px;font-size:11px;text-transform:uppercase;letter-spacing:.06em}
td{padding:7px 10px;border-bottom:1px solid #EDEAE0}
tr:nth-child(even) td{background:#FBFAF5}
.meter{height:8px;background:#E5E1D3;border-radius:6px;min-width:90px}.meter>span{display:block;height:100%;border-radius:6px;background:linear-gradient(90deg,#0FA37F,#7BC96F)}
.bad{color:#B4232A;font-weight:700}.warn{color:#8A5A00;font-weight:700}.ok{color:#0B7A55;font-weight:700}
.sig{display:flex;gap:30px;margin-top:26px}.sig div{flex:1;border-top:1px solid #1C2B24;padding-top:6px;font-size:12px;color:#5B6E64}
footer{margin-top:30px;font-size:11px;color:#5B6E64;border-top:1px solid #DAD6C8;padding-top:10px}
@media print{body{padding:10mm}.k{break-inside:avoid}}
</style>
"""

def html_table(df, meter_col=None):
    if df is None or len(df) == 0:
        return "<p class='meta'>No records in scope.</p>"
    head = "".join(f"<th>{esc(str(c))}</th>" for c in df.columns)
    body = ""
    for _, r in df.iterrows():
        tds = ""
        for c in df.columns:
            v = r[c]
            if meter_col and c == meter_col:
                try:
                    pv = max(0.0, min(100.0, float(v)))
                except (TypeError, ValueError):
                    pv = 0
                cls = "ok" if pv >= 95 else ("warn" if pv >= 80 else "bad")
                tds += f"<td><div class='meter'><span style='width:{pv}%'></span></div><span class='{cls}'>{fnum(pv,1)}%</span></td>"
            else:
                tds += f"<td>{esc('—' if v is None or (isinstance(v,float) and math.isnan(v)) else str(v))}</td>"
        body += f"<tr>{tds}</tr>"
    return f"<table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>"

def report_html(rep):
    ps = rep["per_site"]
    exc = rep["exceptions"]
    exc_view = exc[["id", "site_code", "parameter", "value", "unit", "measured_at", "flags", "status"]].rename(
        columns={"id": "Record", "site_code": "Site", "parameter": "Param", "value": "Value", "unit": "Unit",
                 "measured_at": "Measured", "flags": "Flags", "status": "Status"}) if len(exc) else pd.DataFrame()
    acts = pd.DataFrame(rep["actions"])
    act_view = acts[["id", "site_code", "title", "severity", "status", "assignee", "due_date"]].rename(
        columns={"id": "Action", "site_code": "Site", "title": "Title", "severity": "Severity",
                 "status": "Status", "assignee": "Assignee", "due_date": "Due"}) if len(acts) else pd.DataFrame()
    ev = pd.DataFrame(rep["evidence"])
    ev_view = ev[["id", "site_code", "filename", "kind", "sha256"]].copy() if len(ev) else pd.DataFrame()
    if len(ev_view):
        ev_view["sha256"] = ev_view["sha256"].str[:12] + "…"
        ev_view = ev_view.rename(columns={"id": "Evidence", "site_code": "Site", "filename": "File", "kind": "Kind", "sha256": "SHA-256"})
    appr = "".join(f"<tr><td>{esc(k)}</td><td>{v}</td></tr>" for k, v in rep["approvals"].items())
    draft_note = " · INCLUDING UNAPPROVED DRAFTS" if rep["drafts"] else ""
    return f"""<!DOCTYPE html><html><head><meta charset="utf-8"><title>TerraTrace Report {esc(rep['period'])}</title>{REPORT_CSS}</head><body>
<span class="badge">SYNTHETIC DEMO DATA · DECISION SUPPORT ONLY{draft_note}</span>
<h1>🌿 TerraTrace — Environmental Compliance Report</h1>
<div class="meta">Period <b>{esc(rep['period'])}</b> · Sites: {esc(', '.join(rep['sites']))} · Generated {esc(rep['generated'])} by {esc(rep['actor'])} · Rules {esc(str(rep['versions']['rules']))}</div>
<div class="kpis">
<div class="k"><span>Compliance</span><b>{fnum(rep['pct'],1)}%</b></div>
<div class="k"><span>Readings assessed</span><b>{rep['n_assessed']}</b></div>
<div class="k"><span>Exceedances</span><b class="bad">{rep['n_exc']}</b></div>
<div class="k"><span>Warnings</span><b class="warn">{rep['n_warn']}</b></div>
<div class="k"><span>Open actions</span><b>{len(rep['actions'])}</b></div>
<div class="k"><span>Overdue actions</span><b class="bad">{len(rep['overdue'])}</b></div>
<div class="k"><span>Evidence items</span><b>{len(rep['evidence'])}</b></div>
</div>
<h2>1 · Compliance by site</h2>{html_table(ps, meter_col="Compliance %")}
<h2>2 · Obligation detail (worst reading vs permit limit)</h2>{html_table(rep['per_obl'], meter_col="Compliance %")}
<h2>3 · Exceptions requiring attention (unapproved exceedance / missing / late)</h2>{html_table(exc_view)}
<h2>4 · Open corrective actions</h2>{html_table(act_view)}
<h2>5 · Evidence inventory (files stored outside DB · SHA-256 integrity)</h2>{html_table(ev_view)}
<h2>6 · Approval status of readings in scope</h2><table><thead><tr><th>Status</th><th>Count</th></tr></thead><tbody>{appr}</tbody></table>
<div class="sig"><div>Prepared by: {esc(rep['actor'])}</div><div>Reviewed by: ____________________</div><div>Approved by: ____________________</div></div>
<footer>Lineage: every reading carries source provenance (seed / import file+row / manual / simulator) and batch id in the register.
Versions — rules {esc(str(rep['versions']['rules']))}, factors {esc(str(rep['versions']['factors']))}, schema v{rep['versions']['schema']}.
This report is decision support on synthetic demo data; it is not a regulatory compliance determination. Qualified human approval is required for regulated decisions.</footer>
</body></html>"""

def report_summary(rep):
    lines = [
        f"🌿 TerraTrace compliance snapshot — {rep['period']}",
        f"🏭 Sites: {', '.join(rep['sites'])}",
        f"✅ Compliance: {fnum(rep['pct'],1)}% ({rep['n_assessed'] - rep['n_exc']}/{rep['n_assessed']} readings within permit limits)",
        f"🔴 Open exceedances: {rep['n_exc']} · 🟠 Warnings: {rep['n_warn']}",
        f"🛠 Corrective actions: {len(rep['actions'])} open, {len(rep['overdue'])} overdue",
        f"🗄 Evidence items with SHA-256 integrity: {len(rep['evidence'])}",
        f"🧾 Full audit trail · rules {RULE_VERSION} · generated {rep['generated']}",
        "Synthetic demo data — decision support, built with Streamlit. #EnvironmentalCompliance #EHS #Sustainability",
    ]
    return "\n".join(lines)

def share_links_html(summary):
    q = quote(summary)
    subj = quote("TerraTrace compliance snapshot")
    return f"""<div class="tt-share-row">
<a class="tt-sbtn tt-li" target="_blank" rel="noopener" href="https://www.linkedin.com/feed/?shareActive=true&text={q}">in · Share on LinkedIn</a>
<a class="tt-sbtn tt-x" target="_blank" rel="noopener" href="https://twitter.com/intent/tweet?text={q}">𝕏 · Post</a>
<a class="tt-sbtn tt-wa" target="_blank" rel="noopener" href="https://wa.me/?text={q}">✆ · WhatsApp</a>
<a class="tt-sbtn tt-em" href="mailto:?subject={subj}&body={q}">✉ · Email</a>
</div>"""

def render_share_block(rep, prefix):
    summary = report_summary(rep)
    section("Share this report")
    copy_button(summary, "Copy summary to clipboard")
    st.code(summary, language="text")
    st.caption("The code block above also has a native copy icon (top-right).")
    st.markdown(share_links_html(summary), unsafe_allow_html=True)
    c1, c2, c3 = st.columns(3)
    c1.download_button("⬇ Report (HTML)", report_html(rep).encode("utf-8"),
                       f"terratrace_report_{rep['period']}.html", "text/html", key=f"{prefix}_dl_html")
    csv = rep["df"].to_csv(index=False).encode() if len(rep["df"]) else b"no records"
    c2.download_button("⬇ Register (CSV)", csv, f"terratrace_register_{rep['period']}.csv", "text/csv", key=f"{prefix}_dl_csv")
    acts_csv = pd.DataFrame(rep["actions"]).to_csv(index=False).encode() if rep["actions"] else b"no actions"
    c3.download_button("⬇ Actions (CSV)", acts_csv, f"terratrace_actions_{rep['period']}.csv", "text/csv", key=f"{prefix}_dl_act")
    section("Send to a reviewer (in-app share)")
    if can("submit"):
        with st.form(f"{prefix}_send"):
            rv = st.selectbox("Reviewer", ["M. Okafor", "A. Rivera"], key=f"{prefix}_rv")
            note = st.text_input("Note", "Please review this period's readings and exceptions.", key=f"{prefix}_note")
            if st.form_submit_button("📨 Send validated records for review", disabled=not can("submit")):
                ids = [r["id"] for r in query(
                    f"SELECT id FROM monitoring WHERE deleted=0 AND status='Validated' AND site_code IN ({','.join('?'*len(rep['sites']))})"
                    + (" AND period=?" if rep["period"] != "All periods" else ""),
                    rep["sites"] + ([rep["period"]] if rep["period"] != "All periods" else []))]
                done, _ = transition(ids, "Under Review", note=f"Shared with {rv}: {note}")
                audit("share_for_review", "monitoring", ",".join(done) or "none", f"{len(done)} records sent to {rv}. {note}")
                st.toast(f"📨 Shared with {rv} — {len(done)} records queued for review", icon="✅")
                st.rerun()
    else:
        st.info("Your role can share reports externally, but only Analyst/Admin can queue records for review.")

@st.dialog("🔗 Share center", width="large")
def share_dialog():
    rep = build_report(scope_period(), scope_sites())
    kpis([card("Compliance", f"{fnum(rep['pct'],1)}%", f"{rep['period']}", "ok" if rep["pct"] >= 95 else "warn"),
          card("Exceedances", rep["n_exc"], "in scope", "bad" if rep["n_exc"] else "ok"),
          card("Evidence", len(rep["evidence"]), "SHA-256 tracked", "info")])
    render_share_block(rep, "dlg")
    if st.button("Close", key="dlg_share_close"):
        st.rerun()

# ============================================================ backup / restore / self-checks
def backup_zip():
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        z.write(DB_PATH, "terratrace.db")
        if EVIDENCE_DIR.exists():
            for f in EVIDENCE_DIR.rglob("*"):
                if f.is_file():
                    z.write(f, "evidence/" + str(f.relative_to(EVIDENCE_DIR)).replace("\\", "/"))
    return buf.getvalue()

REQUIRED_TABLES = {"sites", "permits", "obligations", "monitoring", "actions", "evidence", "audit", "imports", "saved_views", "settings"}

def restore_backup(data):
    tmp = BASE_DIR / "_restore_tmp.db"
    ev_files = {}
    if data[:2] == b"PK":
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            if "terratrace.db" not in z.namelist():
                raise ValueError("Zip has no terratrace.db entry.")
            db_bytes = z.read("terratrace.db")
            for n in z.namelist():
                if n.startswith("evidence/") and not n.endswith("/") and ".." not in n:
                    ev_files[n[len("evidence/"):]] = z.read(n)
    else:
        db_bytes = data
    if db_bytes[:16] != b"SQLite format 3\x00":
        raise ValueError("Not a valid SQLite database file.")
    tmp.write_bytes(db_bytes)
    try:
        with closing(sqlite3.connect(tmp)) as c:
            names = {r[0] for r in c.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if not REQUIRED_TABLES.issubset(names):
            raise ValueError(f"Backup schema incomplete — missing: {', '.join(sorted(REQUIRED_TABLES - names))}")
    finally:
        pass
    shutil.copy(DB_PATH, BASE_DIR / "terratrace_pre_restore.bak")
    shutil.move(str(tmp), str(DB_PATH))
    for rel, b in ev_files.items():
        target = EVIDENCE_DIR / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(b)
    audit("restore", "database", "backup", f"Restored DB + {len(ev_files)} evidence files. Previous DB kept as .bak.")

def run_selfchecks():
    results = []
    def check(name, fn):
        try:
            detail = fn()
            results.append({"Check": name, "Result": "✅ PASS", "Detail": detail or ""})
        except Exception as e:
            results.append({"Check": name, "Result": "❌ FAIL", "Detail": str(e)})
    def load_calc():
        assert mass_load_kg_d(5000, 20) == 100.0
        return "5000 m³/d × 20 mg/L ÷ 1000 = 100 kg/d"
    def co2_calc():
        assert co2e_tonnes(100, 3170) == 317.0
        return "100 t × 3170 kg/t ÷ 1000 = 317 tCO2e"
    def max_rules():
        assert classify(130, "max", 125, None)[0] == "exceedance"
        assert classify(120, "max", 125, None)[0] == "warning"
        assert classify(100, "max", 125, None)[0] == "compliant"
        return "130→exceedance · 120→warning · 100→compliant (limit 125, margin 10%)"
    def range_rules():
        assert classify(5.8, "range", 9, 6)[0] == "exceedance"
        assert classify(7.2, "range", 9, 6)[0] == "compliant"
        assert classify(8.9, "range", 9, 6)[0] == "warning"
        return "pH 5.8→exceedance · 7.2→compliant · 8.9→warning (6–9)"
    def missing_rule():
        assert classify(None, "max", 125, None)[0] == "missing"
        return "None → missing (exception path)"
    def unit_norm():
        assert canon_unit("M3/D") == "m³/d" and canon_unit("MG/L") == "mg/L" and canon_unit("dba") == "dB(A)"
        return "M3/D→m³/d · MG/L→mg/L · dba→dB(A)"
    def good_file():
        r = validate_import(pd.read_csv(io.StringIO(SAMPLE_GOOD)), "sample_good.csv")
        assert r["fatal"] is None and r["err"] == 0 and r["ok"] >= 10
        return f"{r['ok']} ok / {r['err']} errors on documented clean sample"
    def bad_file():
        r = validate_import(pd.read_csv(io.StringIO(SAMPLE_BAD)), "sample_flawed.csv")
        assert r["err"] >= 6 and r["dup"] >= 1 and r["ok"] >= 1
        return f"{r['err']} actionable errors · {r['dup']} duplicate skipped · {r['ok']} valid"
    def period_calc():
        assert period_of(date(2026, 11, 13)) == "2026-Q4" and period_of(date(2026, 1, 1)) == "2026-Q1"
        return "2026-11-13→2026-Q4 · 2026-01-01→2026-Q1"
    def db_roundtrip():
        mid = "MON-SELFTEST"
        try:
            exec_sql("INSERT INTO monitoring(id,site_code,parameter,value,unit,measured_at,period,method,source,provenance,batch_id,flags,status,deleted,created_at,updated_at,schema_version) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,0,?,?,?)",
                     (mid, "RVB", "COD", 80.0, "mg/L", now_ts(), CUR_PERIOD, "Lab", "test", "selfcheck", "TEST", "", "Draft", now_ts(), now_ts(), 1))
            r = query("SELECT value FROM monitoring WHERE id=?", (mid,))
            assert r and r[0]["value"] == 80.0
        finally:
            exec_sql("DELETE FROM monitoring WHERE id=?", (mid,))
        assert not query("SELECT 1 FROM monitoring WHERE id=?", (mid,))
        return "insert → read → delete verified, no residue"
    def checksum():
        assert hashlib.sha256(b"abc").hexdigest() == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        return "SHA-256('abc') matches known vector"
    def anomaly_guard():
        z, flag = zscore_anomaly(5.0, [5.0] * 12)
        assert z == 0.0 and not flag
        return "constant history → z=0, no false anomaly"
    def backup_header():
        assert DB_PATH.read_bytes()[:16] == b"SQLite format 3\x00"
        return "live DB header valid — backup source readable"
    for name, fn in [("Domain: mass load (hand-checkable)", load_calc), ("Domain: CO2e factor (hand-checkable)", co2_calc),
                     ("Rules: max-limit boundaries", max_rules), ("Rules: pH range boundaries", range_rules),
                     ("Rules: missing-value exception", missing_rule), ("Units: canonical normalization", unit_norm),
                     ("Import: clean sample accepted", good_file), ("Import: flawed sample rejected with errors", bad_file),
                     ("Dates: reporting-period derivation", period_calc), ("Database: write/read/delete round-trip", db_roundtrip),
                     ("Integrity: SHA-256 known vector", checksum), ("Baseline: anomaly std-guard", anomaly_guard),
                     ("Reliability: DB backup header", backup_header)]:
        check(name, fn)
    return pd.DataFrame(results)

# ============================================================ simulation
def make_sim():
    sim = {"playing": True, "scenario": "Normal operations", "speed": 1.0, "volatility": 1.0,
           "margin": 0.10, "auto_log": setting("auto_log", "1") == "1", "t": 0, "rng": random.Random(7),
           "buffers": {}, "prev": {}, "events": [], "last_auto": {}, "warm": True}
    for sc, pts in SIM_POINTS.items():
        for pc in pts:
            key = f"{sc}|{pc}"
            sim["buffers"][key] = [(NOW - timedelta(seconds=2 * (60 - i)), PARAMS[pc]["base"]) for i in range(60)]
            sim["prev"][key] = "compliant"
    for i in range(60):
        sim_tick(sim, ts=NOW - timedelta(seconds=2 * (60 - i)))
    sim["warm"] = False
    sim["events"] = [{"ts": now_ts(), "kind": "ok", "msg": "Simulation initialized — 18 monitoring points across 4 sites (synthetic)."}]
    return sim

def sim_tick(sim, ts=None):
    ts = ts or datetime.now()
    limits = get_limits()
    mods = SCENARIOS.get(sim["scenario"], {})
    speed, volat = sim["speed"], sim["volatility"]
    for key, buf in sim["buffers"].items():
        sc, pc = key.split("|")
        pdef = PARAMS[pc]
        target = pdef["base"] * mods.get(pc, 1.0)
        v = buf[-1][1]
        v += (target - v) * 0.10 * speed + sim["rng"].gauss(0, pdef["vol"] * volat * (speed ** 0.5))
        v = max(pdef["min"], min(pdef["max"], v))
        if pc == "FLOW":
            v = round(v, 0)
        buf.append((ts, round(v, 3)))
        if len(buf) > 90:
            del buf[0]
        obl = limits.get((sc, pc))
        stt = classify(v, obl["limit_type"], obl["limit_value"], obl["limit_low"], sim["margin"])[0] if obl else "compliant"
        prev = sim["prev"].get(key, "compliant")
        if not sim["warm"] and stt != prev:
            if stt == "exceedance":
                sim["events"].append({"ts": ts.strftime("%H:%M:%S"), "kind": "bad",
                                      "msg": f"🔴 EXCEEDANCE — {sc} {pdef['name']} {fnum(v,2)} {pdef['unit']} (limit {limit_str(obl)})"})
                import time as _t
                if sim["auto_log"] and _t.time() - sim["last_auto"].get(key, 0) > 45:
                    mid = insert_monitoring(sc, pc, v, pdef["unit"], ts.strftime("%Y-%m-%d %H:%M"), "Simulator",
                                            "simulator", f"simulator:{sim['scenario']}:tick {sim['t']}", "SIM-LIVE")
                    audit("auto_capture", "monitoring", mid, f"Live exceedance auto-logged: {sc}/{pc}={v:g}", who="Simulator", role="system")
                    sim["last_auto"][key] = _t.time()
                    sim["events"].append({"ts": ts.strftime("%H:%M:%S"), "kind": "info", "msg": f"📥 Auto-logged {mid} → review queue (Draft)."})
                    old = query("SELECT id FROM monitoring WHERE source='simulator' AND status='Draft' AND deleted=0 ORDER BY created_at DESC")
                    for r in old[30:]:
                        exec_sql("DELETE FROM monitoring WHERE id=?", (r["id"],))
            elif stt == "warning" and prev == "compliant":
                sim["events"].append({"ts": ts.strftime("%H:%M:%S"), "kind": "warn",
                                      "msg": f"🟠 Warning — {sc} {pdef['name']} approaching limit ({fnum(v,2)} {pdef['unit']})."})
            elif stt == "compliant" and prev == "exceedance":
                sim["events"].append({"ts": ts.strftime("%H:%M:%S"), "kind": "ok",
                                      "msg": f"🟢 Back in compliance — {sc} {pdef['name']} ({fnum(v,2)} {pdef['unit']})."})
        sim["prev"][key] = stt
    sim["t"] += 1
    sim["events"] = sim["events"][-14:]

def ensure_state():
    ss = st.session_state
    ss.setdefault("role", "Administrator")
    ss.setdefault("nav", "Live Operations")
    ss.setdefault("g_period", CUR_PERIOD)
    ss.setdefault("g_sites", SITE_CODES)
    ss.setdefault("sim_interval", 2)
    ss.setdefault("sim_site", "RVB")
    ss.setdefault("sim_param", "COD")
    if "sim" not in ss:
        ss.sim = make_sim()

init_db()
ensure_state()

# ============================================================ record / action / obligation dialogs
@st.dialog("🧪 Monitoring record", width="large")
def record_dialog(mid):
    r = query("SELECT * FROM monitoring WHERE id=?", (mid,))
    if not r:
        st.info("Record no longer exists.")
        if st.button("Close", key="rd_gone"):
            st.rerun()
        return
    r = r[0]
    obl = query("SELECT * FROM obligations WHERE id=?", (r["obligation_id"],)) if r["obligation_id"] else []
    obl = obl[0] if obl else get_limits().get((r["site_code"], r["parameter"]))
    ex = explain_record(r, obl)
    st.markdown(f"### {r['id']} · {PARAMS.get(r['parameter'],{}).get('name', r['parameter'])} — {site_label(r['site_code'])}")
    st.markdown(pill(r["status"]) + " " + " ".join(pill(f) for f in (r["flags"] or "").split(",") if f), unsafe_allow_html=True)
    c1, c2 = st.columns(2)
    with c1:
        section("Measurement")
        st.markdown(f"""<table class="tt-table">
<tr><td>Measured value</td><td class="num">{fnum(r['value'],2)} {esc(r['unit'] or '')}</td></tr>
<tr><td>Effective value</td><td class="num">{fnum(ex['effective'],2)} {esc(r['unit'] or '')}{' (override)' if r['override_value'] is not None else ''}</td></tr>
<tr><td>Permit limit</td><td class="num">{esc(limit_str(obl))} {esc(r['unit'] or '')}</td></tr>
<tr><td>Headroom</td><td class="num">{fnum(ex['headroom'],1)}{'%' if ex['headroom'] is not None else ''}</td></tr>
<tr><td>Measured at</td><td class="num">{esc(r['measured_at'])}</td></tr>
<tr><td>Period</td><td>{esc(r['period'])}</td></tr>
<tr><td>Method</td><td>{esc(r['method'])}</td></tr>
<tr><td>Reviewer</td><td>{esc(r['reviewer'] or '—')}</td></tr>
<tr><td>Review note</td><td>{esc(r['review_note'] or '—')}</td></tr></table>""", unsafe_allow_html=True)
        section("Linked evidence & actions")
        ev = query("SELECT * FROM evidence WHERE linked_type='monitoring' AND linked_id=? AND deleted=0", (mid,))
        for e in ev:
            fpath = EVIDENCE_DIR / e["stored_as"]
            cc = st.columns([0.7, 0.3])
            cc[0].markdown(f"🗄️ `{e['id']}` {esc(e['filename'])}")
            if fpath.exists():
                cc[1].download_button("⬇", fpath.read_bytes(), e["filename"], key=f"rd_ev_{e['id']}", help="Download evidence")
        if not ev:
            st.caption("No evidence attached yet.")
        site_ev = query("SELECT id,filename FROM evidence WHERE site_code=? AND deleted=0 AND (linked_id IS NULL OR linked_id!=?)", (r["site_code"], mid))
        if site_ev and can("edit"):
            with st.form("rd_attach"):
                pick = st.selectbox("Attach site evidence", [f"{e['id']} · {e['filename']}" for e in site_ev])
                if st.form_submit_button("📎 Attach", disabled=not can("edit")):
                    eid = pick.split(" · ")[0]
                    exec_sql("UPDATE evidence SET linked_type='monitoring', linked_id=? WHERE id=?", (mid, eid))
                    audit("link_evidence", "evidence", eid, f"Linked to {mid}")
                    st.toast(f"📎 {eid} attached to {mid}", icon="✅")
                    st.rerun()
        acts = query("SELECT * FROM actions WHERE monitoring_id=? AND deleted=0", (mid,))
        for a in acts:
            st.markdown(f"🛠️ `{a['id']}` {esc(a['title'])} — {pill(a['status'])}", unsafe_allow_html=True)
        if can("create") and st.button("➕ Create corrective action from this record", key="rd_newact"):
            st.session_state.act_prefill = {"site": r["site_code"], "mid": mid,
                                            "title": f"{PARAMS.get(r['parameter'],{}).get('name',r['parameter'])} exceedance — {r['site_code']}",
                                            "sev": "High" if "exceedance" in (r["flags"] or "") else "Medium"}
            st.rerun()
    with c2:
        section("Explanation panel")
        st.markdown(f"""<table class="tt-table">
<tr><td>Rule</td><td>{esc(RULE_VERSION)} §1 limit classification (deterministic)</td></tr>
<tr><td>Formula</td><td class="num">status = f(value, limit, margin {float(setting('warn_margin','0.10')):.0%})</td></tr>
<tr><td>Result</td><td>{pill(ex['status'])} — {esc(ex['note'])}</td></tr>
<tr><td>Uncertainty</td><td class="num">±{ex['uncertainty_pct']:.0%} ({esc(r['method'])} method)</td></tr>
<tr><td>Borderline</td><td>{pill('yes — confirm with lab','warn') if ex['borderline'] else pill('no','ok')}</td></tr>
<tr><td>Data quality</td><td>{('<br>'.join(esc(w) for w in ex['warnings'])) or 'No warnings'}</td></tr>
<tr><td>Load context</td><td class="num">{'COD load ≈ ' + fnum(mass_load_kg_d(6200, ex['effective']),1) + ' kg/d @ 6,200 m³/d' if r['parameter']=='COD' and ex['effective'] is not None else 'n/a for this parameter'}</td></tr>
</table>""", unsafe_allow_html=True)
        with st.expander("🧬 Data lineage"):
            st.markdown(f"""- **Provenance:** `{esc(r['provenance'])}`
- **Source:** `{esc(r['source'])}` · **Batch:** `{esc(r['batch_id'] or '—')}`
- **Created:** {esc(r['created_at'])} · **Updated:** {esc(r['updated_at'])} · schema v{r['schema_version']}""")
            imp = query("SELECT * FROM imports WHERE id=?", (r["batch_id"],)) if r["batch_id"] else []
            if imp:
                ip = EVIDENCE_DIR / imp[0]["stored_as"]
                st.caption(f"Original file preserved · SHA-256 `{imp[0]['sha256'][:16]}…`")
                if ip.exists():
                    st.download_button("⬇ Original source file", ip.read_bytes(), imp[0]["filename"], key="rd_src")
        if can("override"):
            with st.expander("✍️ Manual override (audited)"):
                with st.form("rd_override"):
                    ov = st.number_input("Override value", value=float(effective_value(r) or 0.0), format="%.3f")
                    reason = st.text_input("Reason (required, ≥ 5 chars)")
                    if st.form_submit_button("Apply override"):
                        if len(reason.strip()) < 5:
                            st.error("A reason of at least 5 characters is required.")
                        else:
                            exec_sql("UPDATE monitoring SET override_value=?, override_reason=?, flags=?, updated_at=? WHERE id=?",
                                     (float(ov), reason.strip(), flags_for(r["site_code"], r["parameter"], float(ov)), now_ts(), mid))
                            audit("override", "monitoring", mid, f"{fnum(r['value'],2)} → {ov:g}. Reason: {reason}")
                            st.toast("✍️ Override applied — original value preserved", icon="✅")
                            st.rerun()
        if r["status"] == "Under Review" and can("reject"):
            with st.expander("↩️ Reject with reason"):
                with st.form("rd_reject"):
                    reason = st.text_area("Rejection reason (≥ 5 chars)")
                    if st.form_submit_button("Reject record"):
                        done, skip = transition([mid], "Rejected", reason)
                        if done:
                            st.toast(f"↩️ {mid} rejected — correction path opened", icon="✅")
                            st.rerun()
                        else:
                            st.error("; ".join(skip))
    section("Lifecycle actions")
    cols = st.columns(6)
    moves = [("✔ Validate", "Validated", can("submit") and r["status"] == "Draft"),
             ("📤 Submit", "Under Review", can("submit") and r["status"] in ("Draft", "Validated")),
             ("✅ Approve", "Approved", can("approve") and r["status"] in ("Validated", "Under Review")),
             ("🔧 Correct", "Draft", can("edit") and r["status"] in ("Rejected", "Validated", "Under Review")),
             ("📦 Archive", "Archived", can("admin") and r["status"] in ("Approved", "Rejected"))]
    for i, (label, target, enabled) in enumerate(moves):
        if cols[i].button(label, key=f"rd_mv_{target}", disabled=not enabled):
            done, skip = transition([mid], target)
            if done:
                st.toast(f"{label} — {mid} → {target}", icon="✅")
                st.rerun()
            else:
                st.toast("; ".join(skip), icon="⚠️")
    if cols[5].button("🗑 Delete", key="rd_del", disabled=not can("delete")):
        if soft_delete("monitoring", mid):
            st.toast(f"🗑 {mid} deleted — Undo available on the register", icon="🗑")
            st.rerun()
    if st.button("Close", key="rd_close"):
        st.rerun()

@st.dialog("🛠️ Corrective action", width="large")
def action_dialog(aid=None, prefill=None):
    a = None
    if aid:
        rows = query("SELECT * FROM actions WHERE id=?", (aid,))
        a = rows[0] if rows else None
    pre = prefill or {}
    st.markdown(f"### {'Edit ' + a['id'] if a else 'New corrective action'}")
    with st.form("act_form"):
        c1, c2 = st.columns(2)
        site = c1.selectbox("Site", SITE_CODES, index=SITE_CODES.index(a["site_code"] if a else pre.get("site", "RVB")), format_func=site_label)
        title = c2.text_input("Title", a["title"] if a else pre.get("title", ""))
        desc = st.text_area("Description", a["description"] if a else "")
        c3, c4, c5 = st.columns(3)
        sev = c3.selectbox("Severity", ["Low", "Medium", "High", "Critical"], index=["Low", "Medium", "High", "Critical"].index(a["severity"] if a else pre.get("sev", "Medium")))
        asg = c4.selectbox("Assignee", USERS, index=USERS.index(a["assignee"]) if a else 1)
        due = c5.date_input("Due date", date.fromisoformat(a["due_date"]) if a else TODAY + timedelta(days=7))
        mons = query("SELECT id,parameter,measured_at FROM monitoring WHERE site_code=? AND deleted=0 AND flags LIKE '%exceedance%' ORDER BY measured_at DESC LIMIT 20", (site,))
        opts = ["— none —"] + [f"{m['id']} · {m['parameter']} · {m['measured_at']}" for m in mons]
        linked = st.selectbox("Linked exceedance record", opts)
        resolution = st.text_area("Resolution note (required before Verify)", a["resolution"] if a else "")
        save = st.form_submit_button("💾 Save action", disabled=not can("create"))
        if save:
            if len(title.strip()) < 4:
                st.error("Title must be at least 4 characters.")
            else:
                lid = linked.split(" · ")[0] if linked != "— none —" else (a["monitoring_id"] if a else pre.get("mid"))
                if a:
                    exec_sql("UPDATE actions SET site_code=?,title=?,description=?,severity=?,assignee=?,due_date=?,monitoring_id=?,resolution=?,updated_at=? WHERE id=?",
                             (site, title.strip(), desc, sev, asg, due.isoformat(), lid, resolution, now_ts(), aid))
                    audit("edit", "actions", aid, f"Updated: {title}")
                    st.toast(f"💾 {aid} updated", icon="✅")
                else:
                    nid = next_id("actions", "ACT")
                    pri = (query("SELECT COALESCE(MAX(priority),0)+1 p FROM actions")[0]["p"])
                    exec_sql("INSERT INTO actions VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                             (nid, site, lid, title.strip(), desc, sev, int(pri), "Open", asg, due.isoformat(),
                              resolution, None, 0, now_ts(), now_ts(), None, SCHEMA_VERSION))
                    audit("create", "actions", nid, f"{title} ({sev}) due {due}")
                    st.toast(f"🛠️ {nid} created", icon="✅")
                st.rerun()
    if a:
        c1, c2, c3 = st.columns(3)
        if c1.button("✅ Verify closure", key="ad_verify", disabled=not can("verify") or a["status"] != "Resolved"):
            if len((a["resolution"] or "").strip()) < 5:
                st.error("A resolution note (≥ 5 chars) is required before verification.")
            else:
                exec_sql("UPDATE actions SET status='Verified', updated_at=?, resolved_at=? WHERE id=?", (now_ts(), now_ts(), aid))
                audit("verify", "actions", aid, "Closure verified by reviewer.")
                st.toast(f"✅ {aid} verified", icon="✅")
                st.rerun()
        ev = query("SELECT id,filename FROM evidence WHERE site_code=? AND deleted=0", (a["site_code"],))
        if ev:
            pick = c2.selectbox("Attach evidence", [f"{e['id']} · {e['filename']}" for e in ev], key="ad_ev")
            if c2.button("📎 Link", key="ad_link", disabled=not can("edit")):
                eid = pick.split(" · ")[0]
                exec_sql("UPDATE actions SET evidence_id=? WHERE id=?", (eid, aid))
                exec_sql("UPDATE evidence SET linked_type='action', linked_id=? WHERE id=?", (aid, eid))
                audit("link_evidence", "actions", aid, f"Evidence {eid} linked.")
                st.toast("📎 Evidence linked", icon="✅")
                st.rerun()
        if c3.button("🗑 Delete", key="ad_del", disabled=not can("delete")):
            if soft_delete("actions", aid):
                st.toast(f"🗑 {aid} deleted — Undo available", icon="🗑")
                st.rerun()
    if st.button("Close", key="ad_close"):
        st.rerun()

@st.dialog("📜 Obligation", width="large")
def obligation_dialog(oid=None):
    o = query("SELECT * FROM obligations WHERE id=?", (oid,))[0] if oid else None
    st.markdown(f"### {'Edit ' + o['id'] if o else 'New obligation'}")
    limits = get_limits()
    with st.form("obl_form"):
        c1, c2 = st.columns(2)
        site = c1.selectbox("Site", SITE_CODES, index=SITE_CODES.index(o["site_code"]) if o else 0, format_func=site_label)
        kind = c2.selectbox("Kind", ["monitor", "task"], index=0 if (o is None or o["kind"] == "monitor") else 1)
        title = st.text_input("Title", o["title"] if o else "")
        param = None
        lt, hi, lo, unit = "max", 100.0, None, None
        if kind == "monitor":
            param = st.selectbox("Parameter", list(PARAMS.keys()), index=list(PARAMS.keys()).index(o["parameter"]) if o and o["parameter"] else 0,
                                 format_func=lambda p: f"{p} — {PARAMS[p]['name']} ({PARAMS[p]['unit']})")
            pd_ = PARAMS[param]
            unit = pd_["unit"]
            lt = st.selectbox("Limit type", ["max", "min", "range"], index=["max", "min", "range"].index(o["limit_type"]) if o and o["limit_type"] else (2 if pd_["lt"] == "range" else 0))
            hi = st.number_input("Limit (upper / max)" if lt != "min" else "Minimum", value=float(o["limit_value"]) if o and o["limit_value"] is not None else float(pd_["hi"]), format="%.3f")
            if lt == "range":
                lo = st.number_input("Lower bound", value=float(o["limit_low"]) if o and o["limit_low"] is not None else float(pd_["lo"] or 0), format="%.3f")
        c3, c4, c5 = st.columns(3)
        freq = c3.selectbox("Frequency", ["Daily", "Weekly", "Monthly", "Quarterly", "Annual"], index=["Daily", "Weekly", "Monthly", "Quarterly", "Annual"].index(o["frequency"]) if o else 2)
        due = c4.date_input("Next due", date.fromisoformat(o["next_due"]) if o else MONTH_END)
        owner = c5.selectbox("Owner", USERS, index=USERS.index(o["owner"]) if o and o["owner"] in USERS else 1)
        if st.form_submit_button("💾 Save obligation", disabled=not can("edit")):
            if len(title.strip()) < 4:
                st.error("Title must be at least 4 characters.")
            else:
                if o:
                    exec_sql("UPDATE obligations SET site_code=?,kind=?,title=?,parameter=?,unit=?,limit_type=?,limit_value=?,limit_low=?,frequency=?,next_due=?,owner=?,updated_at=? WHERE id=?",
                             (site, kind, title.strip(), param, unit, lt if kind == "monitor" else None,
                              float(hi) if kind == "monitor" else None, float(lo) if lo is not None else None,
                              freq, due.isoformat(), owner, now_ts(), oid))
                    audit("edit", "obligations", oid, f"Updated (limit changes audited; historical flags preserved): {title}")
                    st.toast(f"💾 {oid} updated — future classifications use the new limit", icon="✅")
                else:
                    nid = next_id("obligations", "OBL")
                    exec_sql("INSERT INTO obligations VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                             (nid, site, None, kind, f"{site}-{param or 'TASK'}", title.strip(), param, unit,
                              lt if kind == "monitor" else None, float(hi) if kind == "monitor" else None,
                              float(lo) if lo is not None else None, freq, due.isoformat(), owner, "Open",
                              RULE_VERSION, now_ts(), now_ts(), SCHEMA_VERSION))
                    audit("create", "obligations", nid, title)
                    st.toast(f"📜 {nid} created", icon="✅")
                st.rerun()
    if o and o["kind"] == "task" and can("edit"):
        if st.button("✔ Mark task done", key="od_done", disabled=o["status"] == "Done"):
            exec_sql("UPDATE obligations SET status='Done', updated_at=? WHERE id=?", (now_ts(), oid))
            audit("complete", "obligations", oid, "Task marked done.")
            st.toast(f"✔ {oid} completed", icon="✅")
            st.rerun()
    if st.button("Close", key="od_close"):
        st.rerun()

# ============================================================ pages
def undo_banner():
    u = st.session_state.get("undo")
    if u:
        c1, c2, c3 = st.columns([0.72, 0.14, 0.14])
        c1.markdown(f'<div class="tt-undo">🗑 {esc(u["id"])} deleted (soft). It is hidden everywhere but recoverable.</div>', unsafe_allow_html=True)
        if c2.button("↩️ Undo", key=f"undo_{u['table']}_{u['id']}"):
            rid = undo_delete()
            st.toast(f"↩️ {rid} restored", icon="✅")
            st.rerun()
        if c3.button("Dismiss", key="undo_dismiss"):
            st.session_state.pop("undo", None)
            st.rerun()

def page_live():
    sim = st.session_state.sim
    left, right = st.columns([0.27, 0.73], gap="large")
    with left:
        section("Simulation controls")
        st.caption("Applied live · simulation advances while this page is open.")
        sim["playing"] = st.toggle("▶ Running", value=sim["playing"], key="sim_play")
        sim["scenario"] = st.selectbox("Scenario", list(SCENARIOS.keys()),
                                       index=list(SCENARIOS.keys()).index(sim["scenario"]), key="sim_scen",
                                       help="Storm surge and Treatment upset push parameters toward permit limits.")
        sim["speed"] = st.slider("Simulation speed ×", 0.5, 3.0, sim["speed"], 0.25, key="sim_speed")
        sim["volatility"] = st.slider("Signal volatility ×", 0.2, 3.0, sim["volatility"], 0.1, key="sim_vol")
        st.session_state.sim_interval = st.selectbox("Refresh interval (s)", [1, 2, 3, 5],
                                                     index=[1, 2, 3, 5].index(st.session_state.sim_interval), key="sim_int")
        sim["margin"] = st.slider("Warning margin (%)", 5, 25, int(sim["margin"] * 100), 1, key="sim_margin") / 100
        sim["auto_log"] = st.toggle("Auto-log live exceedances to register", value=sim["auto_log"], key="sim_autolog",
                                    help="Creates Draft records (cooldown 45 s per point) so alerts flow into the review workflow.")
        st.selectbox("Chart site", SITE_CODES, index=SITE_CODES.index(st.session_state.sim_site),
                     format_func=site_label, key="sim_site")
        pts = SIM_POINTS[st.session_state.sim_site]
        if st.session_state.sim_param not in pts:
            st.session_state.sim_param = pts[0]
        st.selectbox("Chart parameter", pts, index=pts.index(st.session_state.sim_param),
                     format_func=lambda p: PARAMS[p]["name"], key="sim_param")
        c1, c2 = st.columns(2)
        if c1.button("⏱ Capture snapshot", key="sim_cap", disabled=not can("create"),
                     help="Commit current values of the charted site as Draft monitoring records."):
            sc = st.session_state.sim_site
            batch = "SIMCAP-" + datetime.now().strftime("%H%M%S")
            n = 0
            for pc in SIM_POINTS[sc]:
                v = sim["buffers"][f"{sc}|{pc}"][-1][1]
                insert_monitoring(sc, pc, v, PARAMS[pc]["unit"], datetime.now().strftime("%Y-%m-%d %H:%M"),
                                  "Simulator", "simulator", f"simulator:{sim['scenario']}:snapshot", batch)
                n += 1
            audit("capture", "monitoring", batch, f"{n} live values captured for {sc}.")
            st.toast(f"⏱ {n} readings captured to register ({batch})", icon="✅")
        if c2.button("↺ Reset sim", key="sim_reset"):
            keep = {k: sim[k] for k in ("playing", "scenario", "speed", "volatility", "margin", "auto_log")}
            st.session_state.sim = make_sim()
            st.session_state.sim.update(keep)
            st.toast("↺ Simulation reset (register records kept)", icon="✅")
            st.rerun()
        rows = []
        sc = st.session_state.sim_site
        for pc in SIM_POINTS[sc]:
            for t, v in sim["buffers"][f"{sc}|{pc}"]:
                rows.append({"time": t.strftime("%Y-%m-%d %H:%M:%S"), "site": sc, "parameter": pc, "value": v, "unit": PARAMS[pc]["unit"]})
        st.download_button("⬇ Export telemetry (CSV)", pd.DataFrame(rows).to_csv(index=False).encode(),
                           f"telemetry_{sc}.csv", "text/csv", key="sim_export")
        st.caption("Synthetic sensor simulation — labelled `Simulator` in provenance. Never mixed silently with lab data.")
    with right:
        interval = float(st.session_state.sim_interval)

        @st.fragment(run_every=interval)
        def live_fragment():
            s = st.session_state.sim
            if s["playing"]:
                sim_tick(s)
            sc = st.session_state.sim_site
            pc = st.session_state.sim_param
            limits = get_limits()
            live_exc = sum(1 for k, stt in s["prev"].items() if stt == "exceedance")
            auto_n = query("SELECT COUNT(*) n FROM monitoring WHERE source='simulator' AND deleted=0")[0]["n"]
            kpis([card("Scenario", esc(s["scenario"]), "live driver", "vio"),
                  card("Sim clock", f"t={s['t']}", "running" if s["playing"] else "paused", "info" if s["playing"] else "mut"),
                  card("Live alerts", live_exc, "points over limit now", "bad" if live_exc else "ok"),
                  card("Sim records", auto_n, "in register (source=simulator)", "info")])
            pts = SIM_POINTS[sc][:4]
            gcols = st.columns(len(pts))
            for i, gpc in enumerate(pts):
                v = s["buffers"][f"{sc}|{gpc}"][-1][1]
                pdef, obl = PARAMS[gpc], limits.get((sc, gpc))
                stt = classify(v, obl["limit_type"], obl["limit_value"], obl["limit_low"], s["margin"])[0] if obl else "compliant"
                color = {"compliant": P["grn"], "warning": P["amb"], "exceedance": P["red"], "missing": P["mut"]}[stt]
                axis_max = 14 if pdef["lt"] == "range" else float(obl["limit_value"]) * 1.35
                gauge = {"axis": {"range": [0, axis_max], "tickcolor": P["mut"]},
                         "bar": {"color": color, "thickness": 0.28}, "bgcolor": "rgba(0,0,0,0)",
                         "borderwidth": 0,
                         "steps": [{"range": [float(obl["limit_value"]) * (1 - s["margin"]), float(obl["limit_value"])],
                                    "color": "rgba(245,184,74,.18)"}] if pdef["lt"] != "range" else
                                   [{"range": [0, float(obl["limit_low"])], "color": "rgba(251,113,133,.18)"},
                                    {"range": [float(obl["limit_value"]), 14], "color": "rgba(251,113,133,.18)"}],
                         "threshold": {"line": {"color": P["red"], "width": 3}, "thickness": 0.8, "value": float(obl["limit_value"])}}
                fig = go.Figure(go.Indicator(mode="gauge+number", value=v,
                                             number={"font": {"size": 22, "color": P["text"]}, "valueformat": ".1f"},
                                             title={"text": f"{pdef['name']}<br><span style='font-size:10px;color:{P['mut']}'>{pdef['unit']} · limit {limit_str(obl)}</span>",
                                                    "font": {"size": 12, "color": P["text"]}}, gauge=gauge))
                fig.update_layout(height=175, margin=dict(l=18, r=18, t=44, b=6), paper_bgcolor="rgba(0,0,0,0)",
                                  font={"color": P["text"], "family": "Space Grotesk"})
                gcols[i].plotly_chart(fig, config={"displayModeBar": False}, key=f"gauge_{gpc}")
            buf = s["buffers"][f"{sc}|{pc}"]
            pdef, obl = PARAMS[pc], limits.get((sc, pc))
            fig = go.Figure()
            fig.add_trace(go.Scatter(x=[t for t, _ in buf], y=[v for _, v in buf], mode="lines", name=pdef["name"],
                                     line=dict(color=P["sky"], width=2.5, shape="spline", smoothing=0.6)))
            if obl and obl["limit_type"] == "range":
                fig.add_hline(y=float(obl["limit_value"]), line_dash="dash", line_color=P["red"],
                              annotation_text=f"Upper {obl['limit_value']:g}", annotation_font_color=P["red"])
                fig.add_hline(y=float(obl["limit_low"]), line_dash="dash", line_color=P["red"],
                              annotation_text=f"Lower {obl['limit_low']:g}", annotation_font_color=P["red"])
            elif obl:
                lim = float(obl["limit_value"])
                fig.add_hrect(y0=lim * (1 - s["margin"]), y1=lim, fillcolor=P["amb"], opacity=0.09, line_width=0)
                fig.add_hline(y=lim, line_dash="dash", line_color=P["red"],
                              annotation_text=f"Permit limit {lim:g} {pdef['unit']}", annotation_font_color=P["red"])
            fig.add_annotation(x=buf[-1][0], y=buf[-1][1], text=f"  {buf[-1][1]:g}", showarrow=False,
                               font=dict(color=P["grn"], size=13), xanchor="left")
            style_fig(fig, 300)
            fig.update_layout(title=dict(text=f"{sc} · {pdef['name']} — live stream ({'running' if s['playing'] else 'paused'})",
                                         font=dict(size=13, color=P["mut"])), showlegend=False)
            st.plotly_chart(fig, config={"displayModeBar": False}, key="live_main")
            lc, rc = st.columns([0.55, 0.45])
            with lc:
                section(f"{sc} — all monitoring points")
                rows = ""
                lims = get_limits()
                for pcode in SIM_POINTS[sc]:
                    v = s["buffers"][f"{sc}|{pcode}"][-1][1]
                    o = lims.get((sc, pcode))
                    stt, head, _ = classify(v, o["limit_type"], o["limit_value"], o["limit_low"], s["margin"]) if o else ("compliant", None, "")
                    rows += (f"<tr><td>{esc(PARAMS[pcode]['name'])}</td><td class='num'>{fnum(v,2)}</td>"
                             f"<td class='num'>{esc(PARAMS[pcode]['unit'])}</td><td class='num'>{esc(limit_str(o))}</td>"
                             f"<td class='num'>{fnum(head,1)}{'%' if head is not None else ''}</td><td>{pill(stt)}</td></tr>")
                st.markdown(f"<table class='tt-table'><thead><tr><th>Parameter</th><th>Value</th><th>Unit</th><th>Limit</th><th>Headroom</th><th>Status</th></tr></thead><tbody>{rows}</tbody></table>", unsafe_allow_html=True)
            with rc:
                section("Event feed")
                feed = "".join(f'<div class="tt-feed-item tt-f-{e["kind"]}"><span class="tt-feed-time">{esc(e["ts"])}</span>{esc(e["msg"])}</div>'
                               for e in reversed(s["events"][-8:]))
                st.markdown(feed or "<span class='tt-note'>Waiting for events…</span>", unsafe_allow_html=True)

        live_fragment()

    section("Period posture — what needs attention")
    sites = scope_sites()
    per = scope_period()
    pq = "AND period=?" if per != "All periods" else ""
    pp = sites + ([per] if per != "All periods" else [])
    mon = query(f"SELECT * FROM monitoring WHERE deleted=0 AND value IS NOT NULL AND site_code IN ({','.join('?'*len(sites))}) {pq}", pp)
    n = len(mon)
    exc = sum(1 for m in mon if "exceedance" in (m["flags"] or ""))
    pct = (n - exc) / n * 100 if n else 0
    overdue_tasks = query(f"SELECT * FROM obligations WHERE kind='task' AND status='Open' AND next_due<? AND site_code IN ({','.join('?'*len(sites))})",
                          [TODAY.isoformat()] + sites)
    overdue_acts = query(f"SELECT * FROM actions WHERE deleted=0 AND status NOT IN ('Resolved','Verified') AND due_date<? AND site_code IN ({','.join('?'*len(sites))})",
                         [TODAY.isoformat()] + sites)
    unreviewed = query(f"SELECT * FROM monitoring WHERE deleted=0 AND flags LIKE '%exceedance%' AND status NOT IN ('Approved','Archived') AND site_code IN ({','.join('?'*len(sites))}) {pq}", pp)
    evn = query(f"SELECT COUNT(*) n FROM evidence WHERE deleted=0 AND site_code IN ({','.join('?'*len(sites))})", sites)[0]["n"]
    kpis([card(f"Compliance · {per}", f"{fnum(pct,1)}%", f"{n-exc}/{n} readings within limits", "ok" if pct >= 95 else "warn"),
          card("Open exceedances", len(unreviewed), "awaiting decision", "bad" if unreviewed else "ok"),
          card("Overdue tasks", len(overdue_tasks), "obligations past due", "bad" if overdue_tasks else "ok"),
          card("Overdue actions", len(overdue_acts), "corrective work late", "bad" if overdue_acts else "ok"),
          card("Evidence items", evn, "SHA-256 tracked", "info"),
          card("Report due", MONTH_END.strftime("%d %b"), f"{(MONTH_END-TODAY).days} days left", "vio")])
    items = []
    for m in unreviewed[:4]:
        items.append(("bad", f"🔴 {m['id']} — {SITE_NAME[m['site_code']]} · {PARAMS.get(m['parameter'],{}).get('name',m['parameter'])} {fnum(m['value'],1)} {m['unit']} ({m['status']})", "Review & Approvals", f"rev_{m['id']}"))
    for t in overdue_tasks[:2]:
        items.append(("warn", f"🕒 {t['id']} — {t['title']} (due {t['next_due']})", "Obligations & Permits", f"task_{t['id']}"))
    for a in overdue_acts[:2]:
        items.append(("warn", f"🛠 {a['id']} — {a['title']} (due {a['due_date']}, {a['status']})", "Corrective Actions", f"act_{a['id']}"))
    if items:
        for kind, msg, page, key in items:
            c1, c2 = st.columns([0.82, 0.18])
            c1.markdown(f'<div class="tt-feed-item tt-f-{kind}">{esc(msg)}</div>', unsafe_allow_html=True)
            c2.button("Open →", key=f"att_{key}", on_click=goto_page, args=(page,))
    else:
        st.success("Nothing overdue in the current scope. 🎉")

def page_obligations():
    sites = scope_sites()
    ph = ",".join("?" * len(sites))
    permits = query(f"SELECT * FROM permits WHERE site_code IN ({ph}) ORDER BY expires", sites)
    obls = query(f"SELECT * FROM obligations WHERE site_code IN ({ph}) ORDER BY next_due", sites)
    n_mon = sum(1 for o in obls if o["kind"] == "monitor" and o["status"] == "Open")
    n_over = sum(1 for o in obls if o["kind"] == "task" and o["status"] == "Open" and o["next_due"] < TODAY.isoformat())
    n_exp = sum(1 for p in permits if (date.fromisoformat(p["expires"]) - TODAY).days <= 30)
    kpis([card("Active monitoring obligations", n_mon, "permit-linked", "info"),
          card("Overdue tasks", n_over, "report / renewal / test", "bad" if n_over else "ok"),
          card("Permits expiring ≤ 30 d", n_exp, "renewal window", "warn" if n_exp else "ok"),
          card("Rule version", RULE_VERSION, "limits audited on change", "vio")])
    section("Permits")
    prow = []
    for p in permits:
        days = (date.fromisoformat(p["expires"]) - TODAY).days
        prow.append({"ID": p["id"], "Site": p["site_code"], "Permit №": p["permit_no"], "Title": p["title"],
                     "Regulator": p["regulator"], "Expires": p["expires"], "Days left": days,
                     "Status": ("🔴 " if days <= 30 else "🟢 ") + p["status"]})
    ev = df_show(pd.DataFrame(prow), hide_index=True, on_select="rerun", selection_mode="single-row", key="perm_tbl")
    if can("admin") and hasattr(ev, "selection") and ev.selection.rows:
        p = permits[ev.selection.rows[0]]
        if st.button(f"🔁 Renew {p['permit_no']} (+365 days)", key="perm_renew"):
            new_exp = (date.fromisoformat(p["expires"]) + timedelta(days=365)).isoformat()
            exec_sql("UPDATE permits SET expires=?, status='Active', updated_at=? WHERE id=?", (new_exp, now_ts(), p["id"]))
            audit("renew", "permits", p["id"], f"Extended to {new_exp}.")
            st.toast(f"🔁 {p['permit_no']} renewed to {new_exp}", icon="✅")
            st.rerun()
    section("Obligations")
    c1, c2, c3, c4 = st.columns([0.3, 0.22, 0.22, 0.26])
    kind_f = c1.selectbox("Kind", ["All", "monitor", "task"], key="obl_kind")
    stat_f = c2.selectbox("Status", ["All", "Open", "Done", "Submitted"], key="obl_stat")
    only_over = c3.toggle("Only overdue", key="obl_over")
    if c4.button("➕ New obligation", key="obl_new", disabled=not can("edit")):
        obligation_dialog(None)
    view = obls
    if kind_f != "All":
        view = [o for o in view if o["kind"] == kind_f]
    if stat_f != "All":
        view = [o for o in view if o["status"] == stat_f]
    if only_over:
        view = [o for o in view if o["status"] == "Open" and o["next_due"] < TODAY.isoformat()]
    if view:
        df = pd.DataFrame([{"ID": o["id"], "Site": o["site_code"], "Kind": o["kind"], "Title": o["title"],
                            "Parameter": o["parameter"] or "—", "Limit": limit_str(o) if o["kind"] == "monitor" else "—",
                            "Unit": o["unit"] or "—", "Frequency": o["frequency"], "Next due": o["next_due"],
                            "Owner": o["owner"], "Status": ("🔴 " if o["status"] == "Open" and o["next_due"] < TODAY.isoformat() else "") + o["status"]}
                           for o in view])
        ev = df_show(df, hide_index=True, on_select="rerun", selection_mode="single-row", key="obl_tbl")
        if hasattr(ev, "selection") and ev.selection.rows:
            oid = view[ev.selection.rows[0]]["id"]
            c1, c2 = st.columns(2)
            if c1.button(f"🔍 Open {oid}", key="obl_open"):
                obligation_dialog(oid)
            o = next(x for x in view if x["id"] == oid)
            if o["kind"] == "task" and c2.button("✔ Mark done", key="obl_done", disabled=not can("edit") or o["status"] == "Done"):
                exec_sql("UPDATE obligations SET status='Done', updated_at=? WHERE id=?", (now_ts(), oid))
                audit("complete", "obligations", oid, "Task marked done.")
                st.toast(f"✔ {oid} done", icon="✅")
                st.rerun()
    else:
        st.info("No obligations match the filters.")
    st.caption("Limit edits are audited and apply to future classifications; historical flags are preserved as evidence.")

def page_monitoring():
    undo_banner()
    section("Monitoring register")
    c1, c2, c3, c4 = st.columns([0.3, 0.24, 0.24, 0.22])
    search = c1.text_input("🔎 Search (id / site / parameter)", key="mon_search")
    stat_f = c2.multiselect("Status", MON_FLOW, key="mon_status")
    flag_f = c3.multiselect("Flags", ["exceedance", "warning", "late", "missing"], key="mon_flags")
    sites_f = c4.multiselect("Sites", SITE_CODES, default=scope_sites(), key="mon_sites")
    c5, c6, c7, c8 = st.columns([0.24, 0.24, 0.26, 0.26])
    meth_f = c5.multiselect("Method", ["Lab", "Sensor", "Manual", "Simulator"], key="mon_meth")
    sort = c6.selectbox("Sort", ["Newest first", "Oldest first", "Value high→low", "Site A→Z"], key="mon_sort")
    page_size = c7.selectbox("Rows", [25, 50, 100, 200], index=1, key="mon_size")
    views = query("SELECT * FROM saved_views ORDER BY name")
    vpick = c8.selectbox("Saved views", ["— apply a saved view —"] + [v["name"] for v in views], key="mon_view")
    if vpick != "— apply a saved view —":
        v = next(x for x in views if x["name"] == vpick)
        payload = json.loads(v["payload"])
        if st.button(f"📂 Apply “{vpick}”", key="mon_applyview"):
            st.session_state.mon_status = payload.get("status", [])
            st.session_state.mon_flags = payload.get("flags", [])
            st.session_state.mon_sites = payload.get("sites", SITE_CODES)
            st.session_state.mon_meth = payload.get("method", [])
            st.session_state.mon_search = payload.get("search", "")
            st.session_state.mon_sort = payload.get("sort", "Newest first")
            st.toast(f"📂 View “{vpick}” applied", icon="✅")
            st.rerun()
    with st.expander("💾 Save current filters as a view"):
        with st.form("mon_saveview"):
            vname = st.text_input("View name")
            if st.form_submit_button("Save view") and vname.strip():
                payload = {"status": stat_f, "flags": flag_f, "sites": sites_f or SITE_CODES, "method": meth_f,
                           "search": search, "sort": sort}
                exec_sql("INSERT OR REPLACE INTO saved_views(name,payload,created_at) VALUES(?,?,?)",
                         (vname.strip(), json.dumps(payload), now_ts()))
                audit("save_view", "saved_views", vname, "Filter preset saved.")
                st.toast(f"💾 View “{vname}” saved", icon="✅")
                st.rerun()
    where, params = ["deleted=0"], []
    per = scope_period()
    if per != "All periods":
        where.append("period=?")
        params.append(per)
    ss = sites_f or SITE_CODES
    where.append(f"site_code IN ({','.join('?'*len(ss))})")
    params += ss
    if stat_f:
        where.append(f"status IN ({','.join('?'*len(stat_f))})")
        params += stat_f
    if meth_f:
        where.append(f"method IN ({','.join('?'*len(meth_f))})")
        params += meth_f
    if flag_f:
        where.append("(" + " OR ".join("flags LIKE ?" for _ in flag_f) + ")")
        params += [f"%{f}%" for f in flag_f]
    if search.strip():
        where.append("(id LIKE ? OR site_code LIKE ? OR parameter LIKE ?)")
        params += [f"%{search.strip()}%"] * 3
    order = {"Newest first": "measured_at DESC", "Oldest first": "measured_at ASC",
             "Value high→low": "value DESC", "Site A→Z": "site_code ASC, measured_at DESC"}[sort]
    rows = query(f"SELECT * FROM monitoring WHERE {' AND '.join(where)} ORDER BY {order} LIMIT {int(page_size)}", params)
    total = query(f"SELECT COUNT(*) n FROM monitoring WHERE {' AND '.join(where)}", params)[0]["n"]
    st.caption(f"{total} records match · showing {len(rows)} · period {per} · lifecycle Draft → Validated → Under Review → Approved / Rejected → Archived")
    if not rows:
        st.info("No records match. Adjust filters or import data in Import Studio.")
        return
    limits = get_limits()
    df = pd.DataFrame([{"ID": r["id"], "Site": r["site_code"], "Parameter": PARAMS.get(r["parameter"], {}).get("name", r["parameter"]),
                        "Value": r["override_value"] if r["override_value"] is not None else r["value"],
                        "Unit": r["unit"], "Limit": limit_str(limits.get((r["site_code"], r["parameter"]))),
                        "Measured": r["measured_at"], "Method": r["method"], "Source": r["source"],
                        "Flags": " ".join(FLAG_EMOJI.get(f, f) for f in (r["flags"] or "").split(",") if f) or "🟢",
                        "Status": r["status"]} for r in rows])
    ev = df_show(df, hide_index=True, on_select="rerun", selection_mode="multi-row", key="mon_tbl",
                 column_config={"Value": st.column_config.NumberColumn(format="%.2f")})
    sel = [rows[i]["id"] for i in ev.selection.rows] if hasattr(ev, "selection") else []
    st.caption(f"{len(sel)} selected" if sel else "Select rows to act on them — or select one and open the detail drawer.")
    b = st.columns(6)
    if b[0].button("🔍 Open detail", key="mon_open", disabled=len(sel) != 1):
        record_dialog(sel[0])
    if b[1].button("📤 Submit for review", key="mon_submit", disabled=not sel or not can("submit")):
        done, skip = transition(sel, "Under Review")
        st.toast(f"📤 {len(done)} submitted · {len(skip)} skipped", icon="✅")
        if skip:
            st.warning("; ".join(skip[:5]))
        st.rerun()
    if b[2].button("✅ Approve", key="mon_approve", disabled=not sel or not can("approve")):
        done, skip = transition(sel, "Approved", note="Bulk approval from register.")
        st.toast(f"✅ {len(done)} approved · {len(skip)} skipped", icon="✅")
        if skip:
            st.warning("; ".join(skip[:5]))
        st.rerun()
    if b[3].button("🗑 Delete", key="mon_del", disabled=not sel or not can("delete")):
        for mid in sel:
            soft_delete("monitoring", mid)
        audit("delete_bulk", "monitoring", ",".join(sel), f"{len(sel)} soft-deleted.")
        st.toast(f"🗑 {len(sel)} deleted — Undo restores the last one", icon="🗑")
        st.rerun()
    sel_rows = [r for r in rows if r["id"] in sel] if sel else rows
    b[4].download_button("⬇ Export CSV", pd.DataFrame(sel_rows).to_csv(index=False).encode(),
                         "monitoring_export.csv", "text/csv", key="mon_export")
    if b[5].button("📤 Share period", key="mon_share"):
        share_dialog()
    if can("create"):
        with st.expander("⚡ Quick entry — add readings in an editable grid"):
            empty = pd.DataFrame({"site_code": ["RVB"] * 4, "parameter": ["COD"] * 4,
                                  "value": [None] * 4, "measured_at": [TODAY] * 4, "method": ["Lab"] * 4})
            try:
                edited = st.data_editor(empty, num_rows="dynamic", width="stretch", key="qe_grid",
                                        column_config={"site_code": st.column_config.SelectboxColumn(options=SITE_CODES),
                                                       "parameter": st.column_config.SelectboxColumn(options=list(PARAMS.keys())),
                                                       "value": st.column_config.NumberColumn(format="%.3f"),
                                                       "measured_at": st.column_config.DateColumn(),
                                                       "method": st.column_config.SelectboxColumn(options=["Lab", "Sensor", "Manual"])})
            except TypeError:
                edited = st.data_editor(empty, num_rows="dynamic", use_container_width=True, key="qe_grid")
            st.caption("Units are derived from the parameter catalog. Rows are validated with the same engine as file imports.")
            if st.button("➕ Validate & add entries", key="qe_add"):
                e = edited.dropna(subset=["value"]).copy()
                if len(e) == 0:
                    st.error("Enter at least one numeric value.")
                else:
                    e["unit"] = e["parameter"].map(lambda p: PARAMS.get(p, {}).get("unit", ""))
                    e["measured_at"] = e["measured_at"].map(lambda d: d.isoformat() if hasattr(d, "isoformat") else str(d))
                    res = validate_import(e[IMP_COLS], "quick-entry")
                    if res["fatal"]:
                        st.error(res["fatal"])
                    else:
                        for v in res["valid"]:
                            insert_monitoring(v["site"], v["param"], v["value"], v["unit"], v["measured_at"],
                                              v["method"], "manual", f"manual:quick-entry:row {v['row']}", "QUICK")
                        audit("create", "monitoring", "quick-entry", f"{res['ok']} added / {res['err']} rejected.")
                        if res["err"]:
                            st.error(f"{res['err']} rows rejected: " + "; ".join(res["errors"]["errors"].tolist()[:4]))
                        if res["ok"]:
                            st.toast(f"⚡ {res['ok']} readings added as Draft", icon="✅")
                            st.rerun()

def page_actions():
    undo_banner()
    sites = scope_sites()
    ph = ",".join("?" * len(sites))
    acts = query(f"SELECT * FROM actions WHERE deleted=0 AND site_code IN ({ph}) ORDER BY priority", sites)
    c1, c2, c3, c4 = st.columns([0.3, 0.24, 0.22, 0.24])
    search = c1.text_input("🔎 Search actions", key="act_search")
    sev_f = c2.multiselect("Severity", ["Low", "Medium", "High", "Critical"], key="act_sev")
    only_over = c3.toggle("Only overdue", key="act_over")
    if c4.button("➕ New action", key="act_new", disabled=not can("create")):
        action_dialog(None)
    if search.strip():
        acts = [a for a in acts if search.lower() in (a["title"] + a["description"] + a["id"]).lower()]
    if sev_f:
        acts = [a for a in acts if a["severity"] in sev_f]
    if only_over:
        acts = [a for a in acts if a["due_date"] < TODAY.isoformat() and a["status"] not in ("Resolved", "Verified")]
    n_open = sum(1 for a in acts if a["status"] == "Open")
    n_prog = sum(1 for a in acts if a["status"] == "In Progress")
    n_over = sum(1 for a in acts if a["due_date"] < TODAY.isoformat() and a["status"] not in ("Resolved", "Verified"))
    n_ver = sum(1 for a in acts if a["status"] == "Verified")
    kpis([card("Open", n_open, "not started", "warn" if n_open else "ok"),
          card("In progress", n_prog, "being worked", "info"),
          card("Overdue", n_over, "past due date", "bad" if n_over else "ok"),
          card("Verified", n_ver, "reviewer-closed", "ok")])
    st.caption("Move cards with ◀ ▶ · reprioritize with ↑ ↓ · Verify requires Reviewer role and a resolution note.")
    cols = st.columns(5)
    sev_kind = {"Low": "mut", "Medium": "info", "High": "warn", "Critical": "bad"}
    for ci, status in enumerate(ACT_FLOW):
        with cols[ci]:
            st.markdown(f"**{pill(status)}**", unsafe_allow_html=True)
            bucket = [a for a in acts if a["status"] == status]
            if not bucket:
                st.caption("— empty —")
            for a in bucket:
                with st.container(border=True):
                    over = a["due_date"] < TODAY.isoformat() and status not in ("Resolved", "Verified")
                    st.markdown(f"**{esc(a['title'])}**  \n{pill(a['severity'], sev_kind[a['severity']])} {pill('OVERDUE', 'bad') if over else ''}", unsafe_allow_html=True)
                    st.caption(f"`{a['id']}` · {a['site_code']} · 👤 {a['assignee']} · due {a['due_date']}" + (f" · 🔗 {a['monitoring_id']}" if a["monitoring_id"] else ""))
                    mv = st.columns(4)
                    idx = ACT_FLOW.index(status)
                    if mv[0].button("◀", key=f"mv_l_{a['id']}", disabled=idx == 0 or not can("edit"), help="Move left"):
                        target = ACT_FLOW[idx - 1]
                        exec_sql("UPDATE actions SET status=?, updated_at=? WHERE id=?", (target, now_ts(), a["id"]))
                        audit("move", "actions", a["id"], f"{status} → {target}")
                        st.rerun()
                    if mv[1].button("▶", key=f"mv_r_{a['id']}", disabled=idx == 4 or not can("edit"), help="Move right"):
                        target = ACT_FLOW[idx + 1]
                        if target == "Verified" and (not can("verify") or len((a["resolution"] or "").strip()) < 5):
                            st.toast("Verify needs Reviewer role + resolution note ≥ 5 chars (open the card).", icon="⚠️")
                        else:
                            exec_sql("UPDATE actions SET status=?, updated_at=?, resolved_at=? WHERE id=?",
                                     (target, now_ts(), now_ts() if target in ("Resolved", "Verified") else a["resolved_at"], a["id"]))
                            audit("move", "actions", a["id"], f"{status} → {target}")
                            st.rerun()
                    if mv[2].button("↑", key=f"mv_u_{a['id']}", disabled=not can("edit"), help="Higher priority"):
                        exec_sql("UPDATE actions SET priority=MAX(1,priority-1) WHERE id=?", (a["id"],))
                        audit("priority", "actions", a["id"], "Priority raised.")
                        st.rerun()
                    if mv[3].button("⋯", key=f"mv_o_{a['id']}", help="Open / edit"):
                        action_dialog(a["id"])

def page_evidence():
    undo_banner()
    sites = scope_sites()
    ph = ",".join("?" * len(sites))
    ev = query(f"SELECT * FROM evidence WHERE deleted=0 AND site_code IN ({ph}) ORDER BY created_at DESC", sites)
    kpis([card("Evidence items", len(ev), "files outside DB · metadata + SHA-256 inside", "info"),
          card("Total size", f"{sum(e['size_bytes'] for e in ev)/1024:.0f} KB", "original bytes preserved", "vio"),
          card("Upload cap", "25 MB", "validated on upload", "mut")])
    if can("create"):
        with st.expander("⬆ Upload evidence", expanded=False):
            with st.form("ev_up"):
                f = st.file_uploader("File (pdf, csv, xlsx, txt, png, jpg)", type=["pdf", "csv", "xlsx", "txt", "png", "jpg"], key="ev_file")
                c1, c2, c3 = st.columns(3)
                site = c1.selectbox("Site", SITE_CODES, format_func=site_label, key="ev_site")
                kind = c2.selectbox("Kind", ["Lab Certificate", "Permit", "Calibration", "Submission", "Maintenance", "Photo", "Other"], key="ev_kind")
                note = c3.text_input("Note", key="ev_note")
                mons = query("SELECT id FROM monitoring WHERE site_code=? AND deleted=0 ORDER BY measured_at DESC LIMIT 40", (site,))
                link = st.selectbox("Link to record (optional)", ["— site level —"] + [m["id"] for m in mons], key="ev_link")
                if st.form_submit_button("📎 Store evidence"):
                    if f is None:
                        st.error("Choose a file first.")
                    else:
                        try:
                            lt, lid = ("monitoring", link) if link != "— site level —" else ("site", site)
                            eid = save_evidence(site, f.name, f.getvalue(), kind, lt, lid, note)
                            st.toast(f"🗄 {eid} stored with SHA-256 checksum", icon="✅")
                            st.rerun()
                        except ValueError as e:
                            st.error(str(e))
    if not ev:
        st.info("No evidence in scope yet.")
        return
    df = pd.DataFrame([{"ID": e["id"], "Site": e["site_code"], "File": e["filename"], "Kind": e["kind"],
                        "Size (KB)": round(e["size_bytes"] / 1024, 1), "SHA-256": e["sha256"][:12] + "…",
                        "Linked": f"{e['linked_type']}:{e['linked_id']}" if e["linked_id"] else "—",
                        "Uploaded by": e["uploaded_by"], "When": e["created_at"]} for e in ev])
    sel = df_show(df, hide_index=True, on_select="rerun", selection_mode="single-row", key="ev_tbl")
    if hasattr(sel, "selection") and sel.selection.rows:
        e = ev[sel.selection.rows[0]]
        section(f"Detail — {e['id']}")
        fpath = EVIDENCE_DIR / e["stored_as"]
        c1, c2, c3, c4 = st.columns(4)
        if fpath.exists():
            c1.download_button("⬇ Download file", fpath.read_bytes(), e["filename"], key="ev_dl")
            if c2.button("🔐 Verify integrity", key="ev_verify"):
                actual = hashlib.sha256(fpath.read_bytes()).hexdigest()
                if actual == e["sha256"]:
                    audit("verify_integrity", "evidence", e["id"], "SHA-256 match.")
                    st.toast("🔐 SHA-256 matches — file intact", icon="✅")
                else:
                    audit("integrity_FAIL", "evidence", e["id"], f"expected {e['sha256'][:12]}… got {actual[:12]}…")
                    st.error("🚨 Checksum mismatch — file altered since upload! Investigate before relying on it.")
        else:
            c1.error("Stored file missing on disk.")
        if c3.button("🗑 Delete", key="ev_del", disabled=not can("delete")):
            if soft_delete("evidence", e["id"]):
                st.toast(f"🗑 {e['id']} hidden — file retained for retention policy", icon="🗑")
                st.rerun()
        if c4.button("🧪 Open linked record", key="ev_open", disabled=e["linked_type"] != "monitoring"):
            record_dialog(e["linked_id"])
        st.caption(f"Full SHA-256: `{e['sha256']}` · note: {e['note'] or '—'}")
    st.download_button("⬇ Checksum manifest (CSV)",
                       pd.DataFrame(ev)[["id", "filename", "sha256", "size_bytes", "site_code"]].to_csv(index=False).encode(),
                       "evidence_manifest.csv", "text/csv", key="ev_manifest")

def page_import():
    section("Import Studio — CSV / Excel with row-level validation")
    st.caption("Pipeline: preview → validate (columns · types · units · ranges · dates · duplicates · referential integrity) → commit valid rows only. Originals preserved with checksums; duplicates skipped on re-import; validated data never silently overwritten.")
    c1, c2, c3 = st.columns(3)
    c1.download_button("⬇ Sample — clean CSV", SAMPLE_GOOD.encode(), "sample_clean.csv", "text/csv", key="imp_good")
    c2.download_button("⬇ Sample — flawed CSV", SAMPLE_BAD.encode(), "sample_flawed.csv", "text/csv", key="imp_bad")
    xbuf = io.BytesIO()
    pd.DataFrame(SAMPLE_GOOD_ROWS, columns=IMP_COLS).to_excel(xbuf, index=False, engine="openpyxl")
    c3.download_button("⬇ Excel template (.xlsx)", xbuf.getvalue(), "import_template.xlsx",
                       "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="imp_xlsx")
    up = st.file_uploader("Upload CSV or XLSX", type=["csv", "xlsx"], key="imp_up")
    b1, b2, b3 = st.columns(3)
    if b1.button("🧪 Try the flawed sample (no upload needed)", key="imp_trybad"):
        st.session_state.imp_df = pd.read_csv(io.StringIO(SAMPLE_BAD))
        st.session_state.imp_name = "sample_flawed.csv"
        st.session_state.imp_bytes = SAMPLE_BAD.encode()
        st.session_state.imp_done = None
        st.rerun()
    if b2.button("✨ Try the clean sample", key="imp_trygood"):
        st.session_state.imp_df = pd.read_csv(io.StringIO(SAMPLE_GOOD))
        st.session_state.imp_name = "sample_clean.csv"
        st.session_state.imp_bytes = SAMPLE_GOOD.encode()
        st.session_state.imp_done = None
        st.rerun()
    if b3.button("♻ Clear preview / allow re-import", key="imp_clear"):
        for k in ("imp_df", "imp_name", "imp_bytes", "imp_done"):
            st.session_state.pop(k, None)
        st.rerun()
    if up is not None:
        meta = (up.name, up.size)
        if st.session_state.get("imp_meta") != meta and st.session_state.get("imp_done") != meta:
            try:
                raw = up.getvalue()
                df = pd.read_csv(io.BytesIO(raw)) if up.name.lower().endswith(".csv") else pd.read_excel(io.BytesIO(raw), engine="openpyxl")
                st.session_state.imp_df, st.session_state.imp_name, st.session_state.imp_bytes = df, up.name, raw
                st.session_state.imp_meta = meta
            except Exception as e:
                LOG.exception("import parse")
                st.error(f"Could not parse '{up.name}': {e}. Use the template above.")
    if st.session_state.get("imp_df") is None:
        st.info("Upload a file or press a **Try sample** button — the validator runs instantly.")
    else:
        res = validate_import(st.session_state.imp_df, st.session_state.imp_name)
        if res["fatal"]:
            st.error(res["fatal"])
        else:
            kpis([card("Rows", res["total"], res["filename"], "info"),
                  card("Valid", res["ok"], "will import as Validated", "ok"),
                  card("Errors", res["err"], "rejected with reasons", "bad" if res["err"] else "ok"),
                  card("Duplicates", res["dup"], "safely skipped", "warn" if res["dup"] else "ok")])
            df_show(res["preview"], hide_index=True, key="imp_preview")
            if res["err"]:
                with st.expander(f"🔴 {res['err']} row errors — actionable detail", expanded=True):
                    for _, e in res["errors"].iterrows():
                        st.markdown(f"- **Row {e['row']}** ({esc(str(e['site_code']))}/{esc(str(e['parameter']))}): {esc(e['errors'])}")
                st.download_button("⬇ Download error report (CSV)", res["errors"].to_csv(index=False).encode(),
                                   "import_errors.csv", "text/csv", key="imp_errdl")
            if st.button(f"📥 Commit {res['ok']} valid rows", key="imp_commit", type="primary",
                         disabled=res["ok"] == 0 or not can("import")):
                batch = commit_import(res, st.session_state.imp_bytes)
                st.session_state.imp_done = (st.session_state.imp_name, len(st.session_state.imp_bytes))
                st.session_state.pop("imp_df", None)
                st.session_state.imp_last = batch
                st.toast(f"📥 {batch}: {res['ok']} imported · {res['err']} errors · {res['dup']} duplicates skipped", icon="✅")
                st.rerun()
    if st.session_state.get("imp_last"):
        c1, c2 = st.columns([0.8, 0.2])
        c1.success(f"Batch **{st.session_state.imp_last}** committed — records are in the register as Validated, with file+row provenance.")
        c2.button("View records →", key="imp_goto", on_click=goto_page, args=("Monitoring Register",))
    section("Import history (originals preserved)")
    hist = query("SELECT * FROM imports ORDER BY ts DESC")
    if hist:
        df_show(pd.DataFrame([{"Batch": h["id"], "File": h["filename"], "SHA-256": h["sha256"][:12] + "…",
                               "Total": h["rows_total"], "OK": h["rows_ok"], "Errors": h["rows_err"],
                               "Dupes": h["rows_dup"], "By": h["actor"], "When": h["ts"], "Status": h["status"]} for h in hist]),
                hide_index=True, key="imp_hist")
        pick = st.selectbox("Re-download an original source file", [h["id"] + " · " + h["filename"] for h in hist], key="imp_orig")
        h = hist[[h["id"] + " · " + h["filename"] for h in hist].index(pick)]
        p = EVIDENCE_DIR / h["stored_as"]
        if p.exists():
            st.download_button("⬇ Original file", p.read_bytes(), h["filename"], key="imp_origdl")

def page_review():
    sites = scope_sites()
    ph = ",".join("?" * len(sites))
    queue = query(f"SELECT * FROM monitoring WHERE deleted=0 AND status IN ('Validated','Under Review') AND site_code IN ({ph}) ORDER BY measured_at DESC", sites)
    exceptions = query(f"SELECT * FROM monitoring WHERE deleted=0 AND (flags LIKE '%missing%' OR flags LIKE '%late%' OR (flags LIKE '%exceedance%' AND status NOT IN ('Approved','Archived'))) AND site_code IN ({ph}) ORDER BY measured_at DESC", sites)
    decided = query(f"SELECT * FROM monitoring WHERE deleted=0 AND status IN ('Approved','Rejected') AND site_code IN ({ph}) ORDER BY updated_at DESC LIMIT 60", sites)
    kpis([card("Awaiting review", len(queue), "Validated + Under Review", "vio" if queue else "ok"),
          card("Exceptions", len(exceptions), "missing · late · open exceedance", "bad" if exceptions else "ok"),
          card("Recently decided", len(decided), "approved / rejected", "ok"),
          card("Your role", st.session_state.role, "approvals need Reviewer/Admin", "info")])
    t1, t2, t3 = st.tabs(["📋 Awaiting review", "⚠️ Exceptions", "🗳 Recently decided"])
    limits = get_limits()
    def review_table(rows, key):
        if not rows:
            st.info("Queue is empty for this scope.")
            return []
        df = pd.DataFrame([{"ID": r["id"], "Site": r["site_code"], "Parameter": r["parameter"],
                            "Value": r["override_value"] if r["override_value"] is not None else r["value"],
                            "Unit": r["unit"], "Limit": limit_str(limits.get((r["site_code"], r["parameter"]))),
                            "Measured": r["measured_at"],
                            "Flags": " ".join(FLAG_EMOJI.get(f, f) for f in (r["flags"] or "").split(",") if f) or "🟢",
                            "Borderline": "⚠︎" if explain_record(r, limits.get((r["site_code"], r["parameter"])))["borderline"] else "",
                            "Status": r["status"]} for r in rows])
        ev = df_show(df, hide_index=True, on_select="rerun", selection_mode="multi-row", key=key,
                     column_config={"Value": st.column_config.NumberColumn(format="%.2f")})
        return [rows[i]["id"] for i in ev.selection.rows] if hasattr(ev, "selection") else []
    with t1:
        st.caption("Borderline ⚠︎ = compliant only within measurement uncertainty — confirm with lab evidence before approving.")
        sel = review_table(queue, "rev_tbl")
        c = st.columns(5)
        if c[0].button("🔍 Open detail", key="rev_open", disabled=len(sel) != 1):
            record_dialog(sel[0])
        if c[1].button(f"✅ Approve {len(sel)}", key="rev_app", disabled=not sel or not can("approve")):
            done, skip = transition(sel, "Approved", note="Approved in review queue.")
            st.toast(f"✅ {len(done)} approved · {len(skip)} skipped", icon="✅")
            if skip:
                st.warning("; ".join(skip[:5]))
            st.rerun()
        if c[2].button("📦 Archive decided", key="rev_arch", disabled=not can("admin")):
            ids = [r["id"] for r in queue if r["status"] == "Approved"]
            done, _ = transition(ids, "Archived")
            st.toast(f"📦 {len(done)} archived", icon="✅")
            st.rerun()
        with st.expander("↩️ Reject selected (reason required)"):
            with st.form("rev_reject"):
                reason = st.text_area("Reason (≥ 5 chars)")
                if st.form_submit_button("Reject", disabled=not sel or not can("reject")):
                    done, skip = transition(sel, "Rejected", reason)
                    if done:
                        st.toast(f"↩️ {len(done)} rejected — correction path opened", icon="✅")
                        st.rerun()
                    else:
                        st.error("; ".join(skip))
        appr = query("SELECT substr(ts,1,10) d, COUNT(*) n FROM audit WHERE action='status:Approved' GROUP BY d ORDER BY d DESC LIMIT 14")
        if appr:
            fig = px.bar(pd.DataFrame(appr).iloc[::-1], x="d", y="n", labels={"d": "Day", "n": "Approvals"},
                         color_discrete_sequence=[P["lime"]])
            style_fig(fig, 220)
            fig.update_layout(title=dict(text="Reviewer throughput — approvals per day", font=dict(size=13, color=P["mut"])))
            st.plotly_chart(fig, config={"displayModeBar": False}, key="rev_thr")
    with t2:
        st.caption("Exception path: missing values stay Draft; late samples are flagged; open exceedances need a corrective action or a review note before approval.")
        sel2 = review_table(exceptions, "exc_tbl")
        if st.button("🔍 Open exception detail", key="exc_open", disabled=len(sel2) != 1):
            record_dialog(sel2[0])
    with t3:
        review_table(decided, "dec_tbl")

def page_reports():
    section("Reports & Share")
    c1, c2, c3 = st.columns([0.25, 0.45, 0.3])
    per = c1.selectbox("Reporting period", [CUR_PERIOD, PREV_PERIOD, "All periods"],
                       index=[CUR_PERIOD, PREV_PERIOD, "All periods"].index(scope_period()) if scope_period() in (CUR_PERIOD, PREV_PERIOD, "All periods") else 0,
                       key="rep_per")
    sites = c2.multiselect("Sites", SITE_CODES, default=scope_sites(), format_func=site_label, key="rep_sites") or SITE_CODES
    drafts = c3.toggle("Include unapproved drafts (watermarked)", value=False, key="rep_drafts")
    rep = build_report(per, sites, drafts)
    kpis([card("Compliance", f"{fnum(rep['pct'],1)}%", f"{rep['n_assessed']} readings assessed", "ok" if rep["pct"] >= 95 else "warn"),
          card("Exceedances", rep["n_exc"], "limit breaches in scope", "bad" if rep["n_exc"] else "ok"),
          card("Warnings", rep["n_warn"], "near-limit readings", "warn" if rep["n_warn"] else "ok"),
          card("Open actions", len(rep["actions"]), f"{len(rep['overdue'])} overdue", "bad" if rep["overdue"] else "info"),
          card("Evidence", len(rep["evidence"]), "integrity-tracked", "vio")])
    ch1, ch2 = st.columns([0.55, 0.45])
    with ch1:
        ps = rep["per_site"]
        if len(ps):
            fig = go.Figure(go.Bar(x=ps["Site"], y=ps["Compliance %"], marker_color=CH[:len(ps)],
                                   text=[f"{v:.1f}%" for v in ps["Compliance %"]], textposition="outside"))
            fig.add_hline(y=95, line_dash="dash", line_color=P["amb"], annotation_text="95% target", annotation_font_color=P["amb"])
            style_fig(fig, 280)
            fig.update_layout(yaxis_range=[0, 108], title=dict(text="Compliance by site (direct labels)", font=dict(size=13, color=P["mut"])))
            st.plotly_chart(fig, config={"displayModeBar": False}, key="rep_site")
    with ch2:
        if rep["approvals"]:
            fig = go.Figure(go.Pie(labels=list(rep["approvals"].keys()), values=list(rep["approvals"].values()),
                                   hole=0.55, marker=dict(colors=[P["grn"], P["vio"], P["mut"], P["red"], P["sky"], P["amb"]]),
                                   textinfo="label+value"))
            style_fig(fig, 280)
            fig.update_layout(title=dict(text="Approval status of readings", font=dict(size=13, color=P["mut"])), showlegend=False)
            st.plotly_chart(fig, config={"displayModeBar": False}, key="rep_appr")
    if len(rep["trend"]):
        tr = rep["trend"]
        fig = go.Figure()
        fig.add_trace(go.Bar(x=tr["week"], y=tr["Exceedances"], name="Exceedances", marker_color=P["red"], opacity=0.75))
        fig.add_trace(go.Scatter(x=tr["week"], y=tr["Compliance %"], name="Compliance %", yaxis="y2",
                                 mode="lines+markers", line=dict(color=P["grn"], width=2.5)))
        fig.update_layout(yaxis2=dict(overlaying="y", side="right", range=[0, 105], title="Compliance %",
                                      gridcolor="rgba(0,0,0,0)"))
        style_fig(fig, 260)
        fig.update_layout(title=dict(text="Weekly trend — compliance vs exceedances", font=dict(size=13, color=P["mut"])))
        st.plotly_chart(fig, config={"displayModeBar": False}, key="rep_trend")
    section("Obligation detail")
    if len(rep["per_obl"]):
        df_show(rep["per_obl"], hide_index=True, key="rep_obl")
    render_share_block(rep, "page")
    with st.expander("👁 Preview the exact HTML report you will download"):
        components.html(report_html(rep), height=560, scrolling=True)
    if can("admin"):
        st.download_button("⬇ Full backup (.zip: DB + evidence)", backup_zip(),
                           f"terratrace_backup_{TODAY.isoformat()}.zip", "application/zip", key="rep_backup")

def page_audit():
    section("Audit trail — immutable log of material events")
    rows = query("SELECT * FROM audit ORDER BY id DESC LIMIT 800")
    c1, c2, c3 = st.columns([0.3, 0.3, 0.4])
    actions = sorted({r["action"] for r in rows})
    af = c1.multiselect("Action", actions, key="aud_action")
    uf = c2.multiselect("Actor", sorted({r["actor"] for r in rows}), key="aud_actor")
    sf = c3.text_input("🔎 Search detail / entity", key="aud_search")
    view = rows
    if af:
        view = [r for r in view if r["action"] in af]
    if uf:
        view = [r for r in view if r["actor"] in uf]
    if sf.strip():
        view = [r for r in view if sf.lower() in (r["detail"] + r["entity"] + r["entity_id"]).lower()]
    kpis([card("Events (recent 800)", len(rows), "approvals · overrides · imports · exports · deletes", "info"),
          card("Matching filters", len(view), "current selection", "vio")])
    if view:
        df_show(pd.DataFrame([{"#": r["id"], "When": r["ts"], "Actor": r["actor"], "Role": r["role"],
                               "Action": r["action"], "Entity": r["entity"], "Entity ID": r["entity_id"],
                               "Detail": r["detail"]} for r in view]), hide_index=True, key="aud_tbl")
        cnt = pd.DataFrame(view)["action"].value_counts().reset_index()
        cnt.columns = ["action", "n"]
        fig = px.bar(cnt.head(10), x="n", y="action", orientation="h", color_discrete_sequence=[P["cyn"]])
        style_fig(fig, 260)
        fig.update_layout(yaxis=dict(autorange="reversed"), title=dict(text="Event mix (filtered)", font=dict(size=13, color=P["mut"])))
        st.plotly_chart(fig, config={"displayModeBar": False}, key="aud_chart")
    st.download_button("⬇ Export audit (CSV)", pd.DataFrame(view).to_csv(index=False).encode(),
                       "audit_trail.csv", "text/csv", key="aud_dl")
    st.caption("Audit rows are append-only in the application layer. Exports, approvals, overrides and deletions are always recorded.")

WORKFLOW_DOT = """
digraph G {
  rankdir=LR; bgcolor="transparent";
  node [shape=box style="rounded,filled" fillcolor="#12241D" color="#2DD4A7" fontcolor="#E8F5EE" fontname="Helvetica" fontsize=11];
  edge [color="#3E6B58" fontcolor="#8FA89B" fontsize=9];
  subgraph cluster_a { label="Actors"; color="#24513F"; fontcolor="#8FA89B";
    "Analyst / Operator"; "Reviewer"; "Administrator"; "Stakeholder (read-only)" [fillcolor="#0F1D17"]; }
  "Data entry (manual / CSV-XLSX import / simulator)" -> "Validation (schema, units, ranges, duplicates)";
  "Validation (schema, units, ranges, duplicates)" -> "Exception queue" [label="missing / late / out-of-range / duplicate" color="#F5B84A"];
  "Exception queue" -> "Correction" [color="#F5B84A"];
  "Correction" -> "Validation (schema, units, ranges, duplicates)" [label="fix & resubmit"];
  "Validation (schema, units, ranges, duplicates)" -> "Validated";
  "Validated" -> "Under review" [label="share to reviewer"];
  "Under review" -> "Approved" [label="approve" color="#2DD4A7"];
  "Under review" -> "Rejected" [label="reject + reason" color="#FB7185"];
  "Rejected" -> "Correction";
  "Approved" -> "Archive / Export / Share";
  "Archive / Export / Share" -> "Stakeholder (read-only)" [color="#38BDF8"];
  "Analyst / Operator" -> "Data entry (manual / CSV-XLSX import / simulator)";
  "Reviewer" -> "Under review";
  "Administrator" -> "Approved" [style=dashed label="override + reason (audited)"];
}
"""
ERD_DOT = """
digraph ERD {
  rankdir=LR; bgcolor="transparent";
  node [shape=record fillcolor="#12241D" style="filled" color="#2DD4A7" fontcolor="#E8F5EE" fontname="Helvetica" fontsize=10];
  edge [color="#3E6B58" fontcolor="#8FA89B" fontsize=9];
  sites [label="{sites|code PK\\lname\\ljurisdiction\\l}"];
  permits [label="{permits|id PK\\lsite_code FK\\lpermit_no\\lexpires\\l}"];
  obligations [label="{obligations|id PK\\lsite_code FK\\lpermit_id FK\\llimit_type / value / low\\lnext_due\\lrule_version\\l}"];
  monitoring [label="{monitoring|id PK\\lobligation_id FK\\lvalue + unit\\lmeasured_at + period\\lflags / status\\lprovenance + batch_id\\loverride_value + reason\\l}"];
  actions [label="{actions|id PK\\lmonitoring_id FK\\lseverity / priority\\lstatus / due_date\\lresolution\\l}"];
  evidence [label="{evidence|id PK\\lfilename + stored_as\\lsha256 + size\\llinked_type + linked_id\\l}"];
  imports [label="{imports|id PK\\lfilename + sha256\\lrow counts\\l}"];
  audit [label="{audit|id PK\\lactor + role\\laction + entity\\ldetail (append-only)\\l}"];
  sites -> permits; sites -> obligations; permits -> obligations;
  obligations -> monitoring; monitoring -> actions; monitoring -> evidence [style=dashed label="linked"];
  imports -> monitoring [style=dashed label="batch lineage"];
}
"""

def page_docs():
    tabs = st.tabs(["📋 Setup files (clipboard)", "📄 Product brief", "🔀 Workflow & data model",
                    "🗂 Backlog & roadmap", "✅ Acceptance & self-checks", "🛡 Security & runbook"])
    # ---------------- setup files
    with tabs[0]:
        section("requirements.txt — copy or download")
        copy_button(REQ_TEXT, "Copy requirements.txt")
        st.code(REQ_TEXT, language="text")
        st.download_button("⬇ requirements.txt", REQ_TEXT.encode(), "requirements.txt", "text/plain", key="doc_req_dl")
        st.caption("No versions pinned in the UI, per your preference. For a reproducible SBOM run: pip freeze > sbom.txt")
        section("app.py — this entire application, copy or download")
        try:
            src = Path(__file__).read_text(encoding="utf-8")
        except Exception:
            src = "# Source could not be read from disk."
        copy_button(src, "Copy app.py (full source)")
        with st.expander("👁 View app.py source (native copy icon at top-right of the block)"):
            st.code(src, language="python")
        st.download_button("⬇ app.py", src.encode(), "app.py", "text/x-python", key="doc_src_dl")
        section("Run commands — Windows PowerShell (each explained)")
        st.code("""python -m venv .venv                  # 1. create an isolated Python environment in this folder
.\\.venv\\Scripts\\Activate.ps1          # 2. activate it (if blocked: Set-ExecutionPolicy -Scope Process RemoteSigned)
pip install -r requirements.txt       # 3. install the 5 open-source libraries — no API keys needed
streamlit run app.py                  # 4. launch the app; browser opens at http://localhost:8501 with live demo data""", language="powershell")
        section("How this single file maps to the target repository structure")
        st.code("""app/core      -> constants, palette, helpers          app/domain   -> classify / mass_load / co2e / explain
app/data      -> SCHEMA, seed, db(), validate_import   app/services -> transition, evidence, reports, backup
app/ui        -> pages + dialogs + live fragment       tests        -> run_selfchecks() (Acceptance tab)
docs          -> this Setup & Docs page                scripts      -> PowerShell commands above""", language="text")
    # ---------------- brief
    with tabs[1]:
        st.markdown(f"""
### One-page product brief — {APP_NAME}
**Problem.** Environmental obligations live in spreadsheets, permits in PDFs, lab results in email, and evidence on shared drives.
Exceedances are found late, reporting periods close in a scramble, and audits stall because nobody can prove *which* file produced *which* number.

**Current workflow & failure points**

| Step today | Failure point |
|---|---|
| Operator copies lab PDFs into Excel | transcription errors, no units check |
| Analyst reconciles vs permit limits manually | limits out of date, exceedances missed |
| Reviewer hunts for the source file | evidence unlinked, approvals unverifiable |
| Manager assembles the period report | days of copy-paste, no lineage |
| Auditor asks "where did this number come from?" | no provenance, no audit trail |

**Buyer (narrow first persona).** A municipal compliance officer (like Dana at Riverbend) responsible for 1–4 sites and quarterly DMR-style reporting;
the expensive workflow is *period close*: chasing readings, limits and evidence into one defensible report.

**Personas & roles**

| Persona | Role | Needs |
|---|---|---|
| Dana, city compliance officer | Analyst | fast entry/import, limit checks, action tracking |
| Miguel, consultancy reviewer | Reviewer | queue, uncertainty flags, approve/reject with reason |
| Priya, EHS manager | Administrator | config, roles, retention, backup, overrides |
| Lena, utility stakeholder | Stakeholder | read-only reports + share |

**In scope (MVP):** sites/permits/obligations · monitoring register with deterministic limit engine · CSV/XLSX import with row-level errors ·
corrective actions · evidence vault with SHA-256 · review/approval lifecycle + audit · period reports + share · SQLite local, backup/restore.
**Out of scope (MVP):** regulatory e-filing, certified compliance determinations, ML predictions on synthetic data, multi-tenant cloud, real sensor integrations (simulator is labelled).

**Measurable success targets (to validate in pilot — not claims):** period-close time −60% · 100% of readings carry provenance ·
0 silent overwrites of validated data · review turnaround < 48 h · identical inputs + rule version ⇒ identical computed results.

**Assumptions & risks:** authoritative permit limits must be entered/verified by a qualified practitioner; demo factors are illustrative;
adoption depends on import quality; single-user SQLite before team edition. See the risk table on the Acceptance tab.
""")
    # ---------------- workflow & data model
    with tabs[2]:
        section("Workflow — actors, entry, review, approval, exceptions")
        try:
            st.graphviz_chart(WORKFLOW_DOT)
        except Exception:
            st.code(WORKFLOW_DOT, language="dot")
        st.markdown("Lifecycle: " + " → ".join(pill(s) for s in MON_FLOW[:5]) + " · correction returns Rejected → Draft · archive after decision.", unsafe_allow_html=True)
        section("Entity relationship diagram (normalized, SQLite → PostgreSQL-ready)")
        try:
            st.graphviz_chart(ERD_DOT)
        except Exception:
            st.code(ERD_DOT, language="dot")
        section("Data dictionary (core fields)")
        dd = [
            ("monitoring.id", "TEXT PK", "—", "stable record id", "MON-####", "system", "Internal", "unique, sequential"),
            ("monitoring.value", "REAL", "per unit", "measured concentration/level", "numeric or NULL", "import/manual/sim", "Internal", "plausible range per parameter; NULL ⇒ missing exception"),
            ("monitoring.unit", "TEXT", "—", "canonical unit", "mg/L · pH · m³/d · mg/m³ · %vol · dB(A) · NTU", "catalog", "Internal", "must match parameter catalog"),
            ("monitoring.measured_at", "TEXT", "local time", "measurement timestamp", "YYYY-MM-DD HH:MM", "source", "Internal", "parseable, not future"),
            ("monitoring.period", "TEXT", "—", "reporting quarter", "YYYY-Qn", "derived", "Internal", "derived from measured_at"),
            ("monitoring.flags", "TEXT", "—", "quality/limit flags", "exceedance, warning, late, missing", "engine", "Internal", f"rule {RULE_VERSION}"),
            ("monitoring.status", "TEXT", "—", "lifecycle state", " · ".join(MON_FLOW), "workflow", "Internal", "transitions guarded by role"),
            ("monitoring.provenance", "TEXT", "—", "lineage pointer", "seed / import:file:row / manual / simulator:tick", "system", "Internal", "always present"),
            ("monitoring.override_value", "REAL", "per unit", "reviewer override", "numeric + reason", "reviewer", "Sensitive", "reason ≥ 5 chars, audited, original preserved"),
            ("obligations.limit_value", "REAL", "per unit", "permit limit (upper/max/min)", "> 0", "permit — qualified entry", "Internal", "changes audited; historical flags preserved"),
            ("obligations.limit_type", "TEXT", "—", "limit semantics", "max · min · range", "permit", "Internal", "range requires limit_low"),
            ("obligations.next_due", "TEXT", "date", "next due date", "YYYY-MM-DD", "permit/frequency", "Internal", "overdue drives attention list"),
            ("evidence.sha256", "TEXT", "hex", "content checksum", "64 hex chars", "hashlib", "Internal", "recomputed on verify"),
            ("evidence.stored_as", "TEXT", "—", "file path outside DB", "evidence_store/…", "system", "Confidential", "bytes never in relational rows"),
            ("actions.priority", "INTEGER", "—", "board ordering", "≥ 1", "user", "Internal", "reorder audited"),
            ("actions.status", "TEXT", "—", "workflow state", " · ".join(ACT_FLOW), "user/reviewer", "Internal", "Verify needs resolution note + Reviewer"),
            ("audit.detail", "TEXT", "—", "event explanation", "free text ≤ 900", "system", "Sensitive", "append-only; no secrets logged"),
            ("imports.sha256", "TEXT", "hex", "original file checksum", "64 hex", "hashlib", "Internal", "original preserved for re-import safety"),
            ("sites.jurisdiction", "TEXT", "—", "regulator/jurisdiction", "free text", "setup", "Internal", "scoping field"),
        ]
        df_show(pd.DataFrame(dd, columns=["Field", "Type", "Unit", "Meaning", "Allowed values", "Source", "Sensitivity", "Validation rule"]),
                hide_index=True, key="doc_dd")
        st.caption(f"Reference catalogs: parameter catalog v1 (units + plausible ranges) · factors {EF_VERSION} — illustrative, verify against an authoritative inventory before regulated use. Every table carries created/updated timestamps + schema_version.")
    # ---------------- backlog
    with tabs[3]:
        c1, c2, c3 = st.columns(3)
        c1.markdown("""**MVP (this build) ✅**
- Sites · permits · obligations
- Live labelled simulation + capture
- Register CRUD · search/filter/sort · saved views
- CSV/XLSX import · preview · row errors · error report
- Deterministic limit engine + explanations
- Corrective action board
- Evidence vault + SHA-256 verify
- Review/approve/reject + overrides
- Audit trail · reports · share center
- SQLite · backup/restore · retention · self-checks""")
        c2.markdown("""**Post-MVP (team edition) 🔜**
- PostgreSQL + authenticated accounts (hashed passwords)
- FastAPI endpoints (Pydantic, pagination, rate limits)
- Real sensor/LIMS adapters (mocked first)
- Uncertainty propagation + anomaly baseline tuning
- Scheduled reports & email delivery
- Multi-site dashboards & SLA alerts
- Concurrent-update tests""")
        c3.markdown("""**Enterprise 🏛**
- SSO / directory integration
- Audit exports & legal hold
- Customer-managed deployment (Docker/Linux)
- Backups with restore drills & monitoring
- API service-level documentation
- Reference-data subscription (licensed, dated factors)
- Qualified domain-review workflow sign-off""")
        section("90-day pilot roadmap (feedback-driven)")
        rm = [("Days 1–14", "Onboard 2 design-partner sites; map their permits & parameters; baseline period-close time"),
              ("Days 15–42", "Harden imports against partner files; measure error rate & review turnaround weekly"),
              ("Days 43–70", "Team edition: PostgreSQL, auth, roles; concurrent-update tests; first shared review"),
              ("Days 71–90", "Validate pricing hypothesis vs measured time saved; scope SSO/enterprise; publish evaluation report")]
        df_show(pd.DataFrame(rm, columns=["Window", "Outcome"]), hide_index=True, key="doc_rm")
        section("Release tiers & pricing hypothesis (to validate — not validated demand)")
        tiers = [("Local evaluation", "Free", "1 operator, synthetic/demo data, community support"),
                 ("Team", "≈ $149 / site / month (hypothesis)", "shared PostgreSQL, roles & approvals, backups, email support"),
                 ("Enterprise", "annual contract (custom)", "SSO, audit exports, deployment controls, SLAs, paid integrations")]
        df_show(pd.DataFrame(tiers, columns=["Tier", "Price", "Includes"]), hide_index=True, key="doc_tiers")
        st.caption("Pricing metric = per active site: aligns with customer value (sites audited) and predictable cost. No compliance certifications are claimed.")
    # ---------------- acceptance
    with tabs[4]:
        section("Measurable acceptance checklist (observable pass/fail)")
        acc = [("Import documented clean sample", "sample_clean.csv → ≥ 10 OK rows, 0 errors", "Auto (self-check) + Import Studio"),
               ("Reject malformed rows with actionable errors", "sample_flawed.csv → ≥ 6 errors, each with row # + fix hint; ≥ 1 duplicate skipped", "Auto + Import Studio"),
               ("Reproducible calculations", "5000×20/1000 = 100 kg/d; 100×3170/1000 = 317 tCO2e; boundary classes exact", "Auto"),
               ("Traceable outputs", "every record shows provenance, batch, rule version, uncertainty, reviewer state", "Record detail drawer"),
               ("Export a report", "Reports & Share → HTML download renders with KPIs, tables, signature block", "Manual, 1 click"),
               ("Share works in-app", "header 🔗 Share → clipboard copy + LinkedIn/email links + send-to-reviewer", "Manual, 1 click"),
               ("Lifecycle enforced", "Stakeholder cannot mutate; exceedance approval blocked without action/note", "Manual role switch"),
               ("Undo destructive action", "delete → Undo restores record; audit shows both events", "Manual"),
               ("Evidence integrity", "upload → verify SHA-256 ✅; altered file → 🚨 mismatch", "Manual"),
               ("Backup / restore", "download .zip → restore → app identical; pre-restore .bak kept", "Runbook tab"),
               ("Clean-DB demo repeatable", "Admin reset → seeded data + simulation restart", "Runbook tab"),
               ("Automated checks pass", "button below → all rows ✅", "Auto")]
        df_show(pd.DataFrame(acc, columns=["Criterion", "Pass condition", "Where observed"]), hide_index=True, key="doc_acc")
        if st.button("▶ Run self-checks now", key="doc_run", type="primary"):
            with st.spinner("Executing validation suite against the live app…"):
                res = run_selfchecks()
            st.session_state.selfcheck = res
            st.session_state.selfcheck_ts = now_ts()
        if "selfcheck" in st.session_state:
            res = st.session_state.selfcheck
            df_show(res, hide_index=True, key="doc_sc")
            fails = int((res["Result"] == "❌ FAIL").sum())
            (st.error if fails else st.success)(f"{len(res)-fails}/{len(res)} checks passed · run at {st.session_state.selfcheck_ts} (executed live, results not pre-recorded)")
        section("Risk register")
        risks = [("Domain validity", "Wrong limits/factors ⇒ wrong compliance picture", "High", "Qualified entry, dated illustrative factors, decision-support framing, human approval"),
                 ("Data quality", "Missing/late/duplicate/out-of-range rows", "High", "Row-level validation, exception queue, uncertainty flags, safe re-import"),
                 ("Security", "Unauthorized approval, evidence tampering", "High", "Role guards in services, SHA-256 verify, append-only audit, secrets in env vars (deployment)"),
                 ("Adoption", "Operators keep spreadsheets", "Medium", "One-click samples, quick entry grid, saved views, pilot time-saved metric"),
                 ("Operational", "DB corruption / lost evidence files", "Medium", "Zip backup incl. files, restore validation, .bak retention, structured logs"),
                 ("Overclaiming", "Demo mistaken for certified compliance", "High", "SYNTHETIC watermark everywhere, no ML claims on synthetic data, approval boundaries documented")]
        df_show(pd.DataFrame(risks, columns=["Risk", "Scenario", "Severity", "Mitigation in this build"]), hide_index=True, key="doc_risks")
    # ---------------- security & runbook
    with tabs[5]:
        section("Access-control matrix (enforced in service functions, not only UI)")
        matrix = [("Create / edit / import / quick entry", "✅", "✅", "—", "—"),
                  ("Submit for review", "✅", "✅", "—", "—"),
                  ("Approve / reject / override / verify", "✅", "—", "✅", "—"),
                  ("Delete (soft) + undo", "✅", "✅ (own drafts)", "—", "—"),
                  ("Config / retention / restore / reset", "✅", "—", "—", "—"),
                  ("Export & share reports", "✅", "✅", "✅", "✅")]
        df_show(pd.DataFrame(matrix, columns=["Capability", "Admin", "Analyst", "Reviewer", "Stakeholder"]), hide_index=True, key="doc_matrix")
        st.markdown("""**Threat model (STRIDE, condensed):** Spoofing → demo role switcher is explicit; production requires authenticated accounts (password hashing library) or SSO.
Tampering → SHA-256 evidence verification + audited overrides. Repudiation → append-only audit of approvals/exports/deletes.
Information disclosure → sensitivity classes in dictionary, no secrets in logs, HTTPS in deployment. DoS → 25 MB upload cap, pagination.
Elevation → role checks inside `transition()` / services. **Human-approval boundary:** the software classifies and explains; only an authorized human approves. Measured vs estimated vs simulated data are always distinguished by `method` + `source`.""")
        section("Operator runbook")
        st.markdown("""1. **Install:** PowerShell commands on the Setup files tab (fresh Windows machine, Python 3.10+).
2. **Daily:** open Live Operations → watch alerts → capture/auto-log → Review queue → approve/reject → period report → 🔗 Share.
3. **Backup:** Reports & Share (Admin) → *Full backup (.zip)* — contains SQLite DB **and** evidence files. Store off-machine.
4. **Restore:** Admin panel below → upload the .zip or .db → schema is validated before swap → previous DB kept as `terratrace_pre_restore.bak`. Re-run self-checks after restore.
5. **Upgrade:** backup → replace app.py → `pip install -r requirements.txt` → run self-checks → compare a known report (regression).
6. **Incident:** check `terratrace.log` (structured JSON lines) + Audit Trail → restore last good backup → record incident in audit.
7. **PostgreSQL migration path:** schema is already normalized with FKs; swap the `db()` helper for a psycopg connection, change AUTOINCREMENT→IDENTITY, run concurrent-update tests, then add FastAPI + auth (post-MVP backlog).""")
        section("60-second demo script (record with Win + G on Windows)")
        st.markdown("""1. Launch → live gauges & stream already running (5 s). 2. Switch scenario to **Storm surge** → watch TSS/COD alerts, auto-logged record (15 s).
3. **Capture snapshot** → open Monitoring Register → filter 🔴 → open detail → explanation panel (15 s).
4. Import Studio → **Try the flawed sample** → row errors → download error report (10 s).
5. Review & Approvals → approve a clean record (5 s). 6. Reports & Share → **🔗 Share** → copy summary / LinkedIn (10 s).""")
        section("License inventory (all permissive, commercial-compatible)")
        lic = [("streamlit", "Apache-2.0", "UI framework"), ("pandas", "BSD-3-Clause", "data frames / import"),
               ("numpy", "BSD-3-Clause", "numerics / baseline stats"), ("plotly", "MIT", "charts"),
               ("openpyxl", "MIT", "Excel read/write"), ("Python stdlib (sqlite3, hashlib, zipfile…)", "PSF", "database, checksums, backup")]
        df_show(pd.DataFrame(lic, columns=["Component", "License", "Purpose"]), hide_index=True, key="doc_lic")
        st.caption("SBOM: run `pip freeze > sbom.txt` in the venv to capture exact installed versions for your records (versions intentionally not shown in the UI).")
        section("Administrator panel")
        if not can("admin"):
            st.info("🔒 Switch to the Administrator role (sidebar) to use backup/restore, retention and reset.")
        else:
            c1, c2 = st.columns(2)
            with c1:
                st.download_button("⬇ Full backup (.zip)", backup_zip(), f"terratrace_backup_{TODAY.isoformat()}.zip",
                                   "application/zip", key="adm_backup")
                up = st.file_uploader("Restore from backup (.zip or .db)", type=["zip", "db"], key="adm_restore")
                if up is not None and st.button("♻ Restore now (validated, previous DB kept)", key="adm_restore_btn"):
                    try:
                        restore_backup(up.getvalue())
                        st.session_state.pop("sim", None)
                        st.toast("♻ Restore complete — re-run self-checks to confirm", icon="✅")
                        st.rerun()
                    except Exception as e:
                        LOG.exception("restore")
                        st.error(f"Restore rejected safely: {e}")
                with st.form("adm_cfg"):
                    margin = st.slider("Warning margin (rule parameter)", 5, 25, int(float(setting("warn_margin", "0.10")) * 100))
                    retention = st.number_input("Retention (days, approved records)", 365, 3650, int(setting("retention_days", "2555")), step=365)
                    if st.form_submit_button("💾 Save configuration"):
                        exec_sql("INSERT OR REPLACE INTO settings VALUES('warn_margin',?)", (f"{margin/100:.2f}",))
                        exec_sql("INSERT OR REPLACE INTO settings VALUES('retention_days',?)", (str(int(retention)),))
                        audit("config", "settings", "rule", f"margin={margin}% retention={retention}d")
                        st.toast("💾 Configuration saved (audited)", icon="✅")
                        st.rerun()
            with c2:
                if st.button("📦 Apply retention (archive old approved records)", key="adm_ret"):
                    cutoff = (TODAY - timedelta(days=int(setting("retention_days", "2555")))).isoformat()
                    ids = query("SELECT id FROM monitoring WHERE status='Approved' AND measured_at<? AND deleted=0", (cutoff,))
                    done, _ = transition([r["id"] for r in ids], "Archived")
                    audit("retention", "monitoring", "batch", f"{len(done)} archived before {cutoff}")
                    st.toast(f"📦 {len(done)} records archived by retention policy", icon="✅")
                confirm = st.checkbox("I understand this wipes the demo database and evidence files")
                if st.button("🧨 Reset demo data (clean re-seed)", key="adm_reset", disabled=not confirm):
                    DB_PATH.unlink(missing_ok=True)
                    shutil.rmtree(EVIDENCE_DIR, ignore_errors=True)
                    init_db()
                    st.session_state.pop("sim", None)
                    ensure_state()
                    audit("reset", "database", "demo", "Clean re-seed from documented generator.")
                    st.toast("🧨 Clean synthetic dataset re-seeded — simulation restarted", icon="✅")
                    st.rerun()
                st.caption("Reset demonstrates the acceptance gate: the full demo repeats from a clean database with documented commands.")

# ============================================================ sidebar / header / dispatch
with st.sidebar:
    st.markdown(f"""<div class="tt-brand"><div class="tt-logo">🌿</div>
<div><div class="tt-brand-name">{APP_NAME}</div><div class="tt-brand-tag">{TAGLINE}</div></div></div>
<div style="margin-top:8px"><span class="tt-badge">SYNTHETIC DEMO</span></div>""", unsafe_allow_html=True)
    st.divider()
    st.radio("Navigation", NAV, format_func=lambda n: f"{NAV_ICON[n]}  {n}", key="nav", label_visibility="collapsed")
    st.divider()
    st.selectbox("👤 Demo role switcher", list(ACTORS.keys()), key="role",
                 help="Production uses authenticated accounts. Guards are enforced in the service layer, not only the UI.")
    st.caption(f"Acting as **{actor()}**")
    st.selectbox("📅 Reporting period", [CUR_PERIOD, PREV_PERIOD, "All periods"], key="g_period")
    st.multiselect("🏭 Sites in scope", SITE_CODES, format_func=site_label, key="g_sites")
    st.divider()
    if st.button("🔗 Share report", key="sb_share", type="primary"):
        share_dialog()
    st.button("📋 Setup files (clipboard)", key="sb_setup", on_click=goto_page, args=("Setup & Docs",))
    sim = st.session_state.sim
    st.caption(f"{'🟢' if sim['playing'] else '⏸'} Sim t={sim['t']} · {sim['scenario']}")
    st.caption("Decision support only — not a regulatory compliance determination.")

hcol1, hcol2 = st.columns([0.78, 0.22])
with hcol1:
    st.markdown(f"""<div class="tt-brand"><div class="tt-logo">🌿</div>
<div><div class="tt-brand-name">{APP_NAME} <span style="font-weight:400;color:{P['mut']};font-size:14px">/ {esc(st.session_state.nav)}</span></div>
<div class="tt-brand-tag">{TAGLINE} · by site & reporting period</div></div></div>""", unsafe_allow_html=True)
with hcol2:
    if st.button("🔗 Share", key="hdr_share", type="primary", help="Copy summary · LinkedIn / X / WhatsApp / Email · send to reviewer · downloads"):
        share_dialog()
st.markdown(f"""<div class="tt-ctx"><span class="tt-dot"></span><span>LIVE</span>
<span>📅 {esc(scope_period())}</span><span>🏭 {len(scope_sites())} sites</span>
<span>🧮 rules {RULE_VERSION}</span><span>👤 {esc(st.session_state.role)}</span>
<span>🗄 SQLite · schema v{SCHEMA_VERSION}</span><span class="tt-badge">SYNTHETIC DEMO DATA</span></div>""", unsafe_allow_html=True)

PAGES = {"Live Operations": page_live, "Obligations & Permits": page_obligations, "Monitoring Register": page_monitoring,
         "Corrective Actions": page_actions, "Evidence Vault": page_evidence, "Import Studio": page_import,
         "Review & Approvals": page_review, "Reports & Share": page_reports, "Audit Trail": page_audit, "Setup & Docs": page_docs}
PAGES[st.session_state.nav]()

if st.session_state.get("act_prefill"):
    pre = st.session_state.pop("act_prefill")
    action_dialog(None, pre)

st.markdown(f"""<div class="tt-note" style="margin-top:26px;border-top:1px solid {P['line']};padding-top:10px">
🌿 {APP_NAME} · open-source MVP · synthetic demo data · deterministic rules {RULE_VERSION} · every number traceable to source · qualified human approval required for regulated decisions.</div>""", unsafe_allow_html=True)

if st.session_state.pop("fresh_seed", False):
    st.toast("🌿 Demo data seeded — simulation is running. Try the 'Storm surge' scenario!", icon="🌿")