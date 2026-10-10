-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_linear_certificate64
-- name    : HlawkaSchatten.DiagonalCutoff.linear_certificate64
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:50:26.382997+00:00
-- url     : https://prove2.me/theorems/a5053436-0353-483f-b0c0-f31dd9bb9bcd
-- title:
--   Linear certificate on $1/65 \le x \le 1/64$
-- statement:
--   On the interval $\frac1{65}\le x\le \frac1{64}$, the cutoff-$65$ numerator model lies above the line of slope $\frac{23}{50}$ relative to the denominator model.
--
--   For every real $x$ in that interval,
--
--   $$
--   x\, N^{\mathrm{lo}}(x) > \frac{23}{50}\, D^{\mathrm{up}}(x),
--   $$
--   where $N^{\mathrm{lo}}$ and $D^{\mathrm{up}}$ are `cutoff65Nlo` and `cutoff65Dup`. At $x=p^{-1}$ this is the comparison $\frac{23}{50}p < C(p)$ on $64\le p\le 65$.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — Bernstein certificate for the cutoff-64 linear slope 23/50.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
open HlawkaSchatten.DiagonalCutoff

theorem HlawkaSchatten.DiagonalCutoff.linear_certificate64 (x : ℝ) (hlo : 1 / 65 ≤ x) (hhi : x ≤ 1 / 64) :
    0 < x * cutoff65Nlo x - (23 / 50) * cutoff65Dup x := by sorry
