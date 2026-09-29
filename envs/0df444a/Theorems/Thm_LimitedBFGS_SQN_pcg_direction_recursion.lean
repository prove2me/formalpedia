-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_direction_recursion
-- name    : LimitedBFGS.SQN.pcg_direction_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T06:53:59.078033+00:00
-- url     : https://prove2.me/theorems/8cb3e3b5-a2f9-4e75-9b88-75b39c06ac37
-- title:
--   Eq. (16) recursion: the direction at index j satisfies g_i^T d_j = -(g_i^T H_0 g_j) + beta (g_i^T d_{j-1})
-- statement:
--   Let f(x) = 1/2 x^T A x + b^T x on R^n with A symmetric positive definite, H_0 a fixed symmetric positive definite preconditioner, and x_0 in R^n. Run the preconditioned conjugate gradient method with fixed preconditioner H_0 and exact line searches from x_0, with iterates x_i, directions d_i and gradients g_i = A x_i + b, so that d_0 = -H_0 g_0, x_{i+1} = x_i + a_i d_i and d_{j} = -H_0 g_j + beta_{j-1} d_{j-1} with beta_{j-1} = y_{j-1}^T H_0 g_j / y_{j-1}^T d_{j-1} and y_{j-1} = g_j - g_{j-1}. Then for every pair of indices with i != j and j >= 1, g_i^T d_j = -(g_i^T H_0 g_j) + beta_{j-1} (g_i^T d_{j-1}). This is the direction recurrence paired with g_i. It is what makes the second relation of eq. (16), g_i^T d_j = 0 for j < i, a downward induction on j from the first relation g_i^T H_0 g_j = 0 for i != j, with no independent hypothesis of its own. The statement is unconditional: the denominator is the one the definition itself divides by, so nothing here divides by the line-search step a_j and no case split on a_j = 0 is needed.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13) and eq. (16): the direction recurrence d_j = -H_0 g_j + beta_{j-1} d_{j-1} paired with a gradient, which turns the two relations of eq. (16) into one induction.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (16), p. 777, the recursion that connects the two relations: for `i != j` and
`0 < j`, the direction at `j` satisfies

    g_iᵀ d_j  =  -(g_iᵀ H₀ g_j)  +  beta * (g_iᵀ d_{j-1}),

where `beta` is exactly the step coefficient the definition of the iteration attaches to
the move from `pcgIter … (j-1)` to `pcgIter … j`. This is the direction recurrence
`d_{j+1} = -H₀ g_{j+1} + beta_j d_j` read at the index `j`, paired with `g_i`.

**Why it matters.** It makes the second relation of eq. (16) — `g_iᵀ d_j = 0` for `j < i` —
a *downward induction on `j`* from the first relation `g_iᵀ H₀ g_j = 0` for `i != j`, with no
independence hypothesis of its own. Fix `i >= 1`. The base case `j = 0` is
`g_iᵀ d_0 = -(g_iᵀ H₀ g_0)`, which is the first relation at the pair `(i, 0)`; the
induction step uses the first relation at `(i, j)` together with `g_iᵀ d_{j-1} = 0`. So
`LimitedBFGS.SQN.pcg_orthogonality` reduces to the single relation
`LimitedBFGS.SQN.pcg_grad_orthogonality`, rather than needing both proved separately.

The statement is unconditional in the step coefficient: the denominator
`y ⬝ᵥ stp.d` is the one the definition itself divides by, so nothing here divides by the
line-search step `a_j` and no case split on `a_j = 0` is required. -/
theorem pcg_direction_recursion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (i j : ℕ) (hne : i ≠ j)
    (hj : 0 < j) :
    let stp := pcgIter A b H₀ x₀ (j - 1)
    let gj := grad A b (pcgIter A b H₀ x₀ j).x
    let gp := grad A b stp.x
    let y := gj - gp
    grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d
      = -(grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ gj))
        + ((y ⬝ᵥ (H₀ *ᵥ gj)) / (y ⬝ᵥ stp.d))
            * (grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ stp.d) := by sorry

end LimitedBFGS.SQN
