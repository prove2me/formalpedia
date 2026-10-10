-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_envelope_certificate64
-- name    : HlawkaSchatten.DiagonalCutoff.envelope_certificate64
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:50:24.761159+00:00
-- url     : https://prove2.me/theorems/6fe15a69-8990-4db4-ae7b-5691fd992f56
-- title:
--   Envelope certificate on $1/65 \le x \le 1/64$
-- statement:
--   On the interval $\frac1{65}\le x\le \frac1{64}$, the cutoff-$65$ numerator and root models dominate the scalar envelope at radius $\frac{91}{250}$.
--
--   Let $N^{\mathrm{lo}}$, $D^{\mathrm{up}}$, and $G^{\mathrm{lo}}$ be the three rational models `cutoff65Nlo`, `cutoff65Dup`, and `cutoff65Glo`. For every real $x$ in that interval,
--
--   $$
--   N^{\mathrm{lo}}(x)\,\bigl(2G^{\mathrm{lo}}(x)\bigr) > \left(1-\frac{91}{250}\right) D^{\mathrm{up}}(x).
--   $$
--
--   This is the polynomial input to the comparison of the scalar envelope at $\frac{91}{250}$ with the cyclic constant on $64\le p\le 65$. The models themselves are the same formulas already used at cutoff $65$; only the interval has moved.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — Bernstein certificate for the cutoff-64 scalar envelope at radius 91/250.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
open HlawkaSchatten.DiagonalCutoff

theorem HlawkaSchatten.DiagonalCutoff.envelope_certificate64 (x : ℝ) (hlo : 1 / 65 ≤ x) (hhi : x ≤ 1 / 64) :
    0 < cutoff65Nlo x * (2 * cutoff65Glo x) - (1 - 91 / 250) * cutoff65Dup x := by sorry
