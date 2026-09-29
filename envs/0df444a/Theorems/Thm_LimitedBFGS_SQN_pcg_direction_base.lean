-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_direction_base
-- name    : LimitedBFGS.SQN.pcg_direction_base
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:33:27.944985+00:00
-- url     : https://prove2.me/theorems/441890a2-5fb8-49fc-965a-3bef5f01d1d2
-- title:
--   Eq. (16) base case: the initial direction is d_0 = -H0 g_0, so g_i^T d_0 = -(g_i^T H0 g_0) for i nonzero
-- statement:
--   Let f(x) = 1/2 x^T A x + b^T x on R^n with A symmetric positive definite, H_0 a fixed symmetric positive definite preconditioner, and x_0 in R^n. Run the preconditioned conjugate gradient method with fixed preconditioner H_0 and exact line searches from x_0, with iterates x_i, directions d_i and gradients g_i = A x_i + b. The initial direction is exactly d_0 = -H_0 g_0, by the zeroth clause of the iteration. Hence for every index i that is nonzero, g_i^T d_0 = -(g_i^T H_0 g_0). This is the base case of the downward induction that carries the second relation of eq. (16), g_i^T d_j = 0 for j < i, and it is exactly the first relation of eq. (16) read at the index pair (i, 0). The case i = 0 is excluded because the half-line j < i then forces i >= 1, so the base case is only ever needed for nonzero i.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13) at its zeroth clause d_0 = -H_0 g_0, paired with eq. (16) at the index pair (i, 0). Together with the direction recursion this is what makes the second relation of eq. (16) a downward induction on j from the first.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- The base case of the downward induction that carries eq. (16)'s second relation:
the initial direction is exactly `d_0 = -(H0 *ᵥ g_0)`, so for every nonzero `i`,

    g_i ⬝ᵥ d_0  =  -(g_i ⬝ᵥ (H0 *ᵥ g_0)).

Together with the already-proved child `pcg_direction_recursion`, which gives the
step from `j - 1` to `j`, this is all that is needed to read
`LimitedBFGS.SQN.pcg_orthogonality`'s second conjunct as a downward induction on
`j` from its first. -/
theorem pcg_direction_base {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (i : ℕ) (hne : i ≠ 0) :
    grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ 0).d
      = -(grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ
            (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ 0).x)) := by sorry

end LimitedBFGS.SQN
