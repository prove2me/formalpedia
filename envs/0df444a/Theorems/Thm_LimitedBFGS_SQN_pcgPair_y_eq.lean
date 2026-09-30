-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcgPair_y_eq
-- name    : LimitedBFGS.SQN.pcgPair_y_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T21:09:42.432408+00:00
-- url     : https://prove2.me/theorems/b990e0b5-8cbe-4d2c-8580-6482b9d63a36
-- title:
--   The stored gradient difference of a PCG pair is the line-search step times the curvature step
-- statement:
--   Let `pcgPair A b H₀ x₀ k = (s_k, y_k)` be the secant pair stored after the step from `x_k`, on the quadratic `f(x) = ½ xᵀAx + bᵀx` with `g(x) = Ax + b`.
--
--   **Claim.** `y_k = A s_k`.
--
--   **Why.** `y_k = g_{k+1} - g_k = A(x_{k+1} - x_k) = A s_k`, since the gradient of this quadratic is the affine map `x ↦ Ax + b`.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 775, Property (b).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- The second component of `pcgPair A b H₀ x₀ k` is `y_k = grad A b x_{k+1} - grad A b x_k`,
and on the quadratic `grad A b (x_{k+1} - x_k) = A *ᵥ s_k`. -/
theorem pcgPair_y_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    (pcgPair A b H₀ x₀ k).2
      = A *ᵥ (pcgPair A b H₀ x₀ k).1 := by sorry

end LimitedBFGS.SQN
