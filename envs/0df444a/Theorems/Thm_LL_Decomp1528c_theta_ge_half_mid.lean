-- Prove2me | Theorems.Thm_LL_Decomp1528c_theta_ge_half_mid
-- name    : LL_Decomp1528c.theta_ge_half_mid
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:29:53.52456+00:00
-- url     : https://prove2.me/theorems/827eac42-d6ba-48fb-9e92-13cb0776e11d
-- title:
--   Middle natural range for the half-theta bound
-- statement:
--   For every natural number $n$ with $1000\le n<10^4$, $\theta(n)\ge(n+1)/2$.
-- source:
--   Lab unit U-1528, classical Chebyshev bounds; source context: P. J. Campbell 2026, https://arxiv.org/abs/2608.09488v1. Exact range and constant as stated in Decomp1528c.lean.

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528c
theorem theta_ge_half_mid (n : ℕ) (h1 : 1000 ≤ n) (h2 : n < 10 ^ 4) : ((n : ℝ) + 1) / 2 ≤ θ n := by sorry
end LL_Decomp1528c
