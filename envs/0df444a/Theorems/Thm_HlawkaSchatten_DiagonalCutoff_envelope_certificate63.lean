-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_envelope_certificate63
-- name    : HlawkaSchatten.DiagonalCutoff.envelope_certificate63
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:14:53.765356+00:00
-- url     : https://prove2.me/theorems/a1fdec29-db8b-4ff8-99ea-bf6f93d88a32
-- title:
--   Envelope certificate on $1/64 \le x \le 1/63$
-- statement:
--   On the interval $\frac1{64}\le x\le \frac1{63}$, the cutoff-$65$ numerator and root models dominate the scalar envelope at radius $\frac{91}{250}$.
--
--   Let $N^{\mathrm{lo}}$, $D^{\mathrm{up}}$, and $G^{\mathrm{lo}}$ be the three rational models `cutoff65Nlo`, `cutoff65Dup`, and `cutoff65Glo`. For every real $x$ in that interval,
--
--   $$
--   N^{\mathrm{lo}}(x)\,\bigl(2G^{\mathrm{lo}}(x)\bigr) > \left(1-\frac{91}{250}\right) D^{\mathrm{up}}(x).
--   $$
--
--   This is the polynomial input to the comparison of the scalar envelope at $\frac{91}{250}$ with the cyclic constant on $63\le p\le 64$. The models themselves are unchanged; only the interval has moved.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — Bernstein certificate for the cutoff-63 scalar envelope at radius 91/250.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
open HlawkaSchatten.DiagonalCutoff

theorem HlawkaSchatten.DiagonalCutoff.envelope_certificate63 (x : ℝ) (hlo : 1 / 64 ≤ x) (hhi : x ≤ 1 / 63) :
    0 < cutoff65Nlo x * (2 * cutoff65Glo x) - (1 - 91 / 250) * cutoff65Dup x := by sorry
