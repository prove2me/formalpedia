-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_linear_certificate62
-- name    : HlawkaSchatten.DiagonalCutoff.linear_certificate62
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:38:30.028607+00:00
-- url     : https://prove2.me/theorems/e37e129d-3faa-40aa-b95f-93cc53057ec9
-- title:
--   Linear certificate on $1/63 \le x \le 1/62$
-- statement:
--   On the interval $\frac1{63}\le x\le \frac1{62}$, the numerator model lies above the line of slope $\frac{23}{50}$ relative to the denominator model.
--
--   For every real $x$ in that interval,
--
--   $$
--   x\, N^{\mathrm{lo}}(x) > \frac{23}{50}\, D^{\mathrm{up}}(x).
--   $$
--   At $x=p^{-1}$ this is the comparison $\frac{23}{50}p < C(p)$ on $62\le p\le 63$.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — Bernstein certificate for the cutoff-62 linear slope 23/50.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
open HlawkaSchatten.DiagonalCutoff

theorem HlawkaSchatten.DiagonalCutoff.linear_certificate62 (x : ℝ) (hlo : 1 / 63 ≤ x) (hhi : x ≤ 1 / 62) :
    0 < x * cutoff65Nlo x - (23 / 50) * cutoff65Dup x := by sorry
