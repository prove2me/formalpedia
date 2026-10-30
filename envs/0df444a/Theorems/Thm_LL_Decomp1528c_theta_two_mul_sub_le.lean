-- Prove2me | Theorems.Thm_LL_Decomp1528c_theta_two_mul_sub_le
-- name    : LL_Decomp1528c.theta_two_mul_sub_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:31:03.311973+00:00
-- url     : https://prove2.me/theorems/47b0103b-db29-4e19-939c-54242c13a77e
-- title:
--   Theta increment at a doubled natural argument
-- statement:
--   For every natural number $n$, $\theta(2n)-\theta(n)\le n\log4$, including $n=0$.
-- source:
--   Lab unit U-1528, classical Chebyshev bounds; source context: P. J. Campbell 2026, https://arxiv.org/abs/2608.09488v1. Chebyshev 1852; Hardy and Wright, Theorem 415 proof, as cited in the lab.

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528c
theorem theta_two_mul_sub_le (n : ℕ) : θ (2 * n) - θ n ≤ n * log 4 := by sorry
end LL_Decomp1528c
