-- Prove2me | Theorems.Thm_LL_Decomp1528b_integral_A_sub
-- name    : LL_Decomp1528b.integral_A_sub
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:08:29.390784+00:00
-- url     : https://prove2.me/theorems/4de07b84-31f8-4c82-888a-8f63dc23cbf9
-- title:
--   Integral error bound against log log
-- statement:
--   For real $x,y$ with $2\le y\le x$, with $A(t)=\sum_{p\le \lfloor t\rfloor}\log p/p$, $\left|\int_y^x A(t)/(t\log^2 t)\,dt-(\log\log x-\log\log y)\right|\le 2\,(1/\log y-1/\log x)$.
-- source:
--   P. J. Campbell, arXiv 2608.09488 v1 (2026), Section 4; comparison with Rosser and Schoenfeld, Illinois J. Math. 6 (1962), p. 70.

import Mathlib

open Real Finset Filter Topology

namespace LL_Decomp1528b
theorem integral_A_sub {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |(∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2)) -
        (log (log x) - log (log y))| ≤ 2 * (1 / log y - 1 / log x) := by sorry
end LL_Decomp1528b
