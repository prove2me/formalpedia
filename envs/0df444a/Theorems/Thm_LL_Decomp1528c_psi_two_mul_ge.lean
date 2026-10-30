-- Prove2me | Theorems.Thm_LL_Decomp1528c_psi_two_mul_ge
-- name    : LL_Decomp1528c.psi_two_mul_ge
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:31:20.350351+00:00
-- url     : https://prove2.me/theorems/dfc26d21-795a-4b57-b0a9-a2c72cff17fb
-- title:
--   Psi lower bound at even natural arguments
-- statement:
--   For every natural number $n\ge1$, $\psi(2n)\ge n\log4-\log(2n+1)$.
-- source:
--   Lab unit U-1528, classical Chebyshev bounds; source context: P. J. Campbell 2026, https://arxiv.org/abs/2608.09488v1. Chebyshev 1852; Hardy and Wright, Theorem 414 proof, as cited in the lab.

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528c
theorem psi_two_mul_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * log 4 - log (2 * n + 1) ≤ ψ (2 * n) := by sorry
end LL_Decomp1528c
