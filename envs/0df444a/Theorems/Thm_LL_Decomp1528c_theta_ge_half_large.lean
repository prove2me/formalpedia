-- Prove2me | Theorems.Thm_LL_Decomp1528c_theta_ge_half_large
-- name    : LL_Decomp1528c.theta_ge_half_large
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:29:41.767602+00:00
-- url     : https://prove2.me/theorems/85b0a73e-dc03-4be4-8480-bf1abeb848a2
-- title:
--   Large natural range for the half-theta bound
-- statement:
--   For every natural number $n\ge10^4$, $\theta(n)\ge(n+1)/2$.
-- source:
--   Lab unit U-1528, classical Chebyshev bounds; source context: P. J. Campbell 2026, https://arxiv.org/abs/2608.09488v1. Lab large-range formulation; comparison cited in the lab: Rosser and Schoenfeld 1962, equation 3.14, p. 70.

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528c
theorem theta_ge_half_large (n : ℕ) (hn : 10 ^ 4 ≤ n) : ((n : ℝ) + 1) / 2 ≤ θ n := by sorry
end LL_Decomp1528c
