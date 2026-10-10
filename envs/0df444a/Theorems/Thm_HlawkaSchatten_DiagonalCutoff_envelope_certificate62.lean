-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_envelope_certificate62
-- name    : HlawkaSchatten.DiagonalCutoff.envelope_certificate62
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:38:33.676298+00:00
-- url     : https://prove2.me/theorems/b43d1ddf-ef61-4a44-8ed5-d0785b6e9b59
-- title:
--   Envelope certificate on $1/63 \le x \le 1/62$
-- statement:
--   On the interval $\frac1{63}\le x\le \frac1{62}$, the cutoff-$65$ numerator and root models dominate the scalar envelope at radius $\frac{3643}{10000}$.
--
--   Let $N^{\mathrm{lo}}$, $D^{\mathrm{up}}$, and $G^{\mathrm{lo}}$ be `cutoff65Nlo`, `cutoff65Dup`, and `cutoff65Glo`. For every real $x$ in that interval,
--
--   $$
--   N^{\mathrm{lo}}(x)\,\bigl(2G^{\mathrm{lo}}(x)\bigr) > \left(1-\frac{3643}{10000}\right) D^{\mathrm{up}}(x).
--   $$
--
--   The models are unchanged. Only the interval and the confinement radius have moved. This is the polynomial input to the scalar comparison on $62\le p\le 63$.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — Bernstein certificate for the cutoff-62 scalar envelope at radius 3643/10000.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
open HlawkaSchatten.DiagonalCutoff

theorem HlawkaSchatten.DiagonalCutoff.envelope_certificate62 (x : ℝ) (hlo : 1 / 63 ≤ x) (hhi : x ≤ 1 / 62) :
    0 < cutoff65Nlo x * (2 * cutoff65Glo x) - (1 - 3643 / 10000) * cutoff65Dup x := by sorry
