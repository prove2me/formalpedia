-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_direction_A_conjugacy
-- name    : LimitedBFGS.SQN.pcg_direction_A_conjugacy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T09:14:13.690976+00:00
-- url     : https://prove2.me/theorems/2fd54768-b73c-40dc-b828-215fe20f7a0f
-- title:
--   Along the PCG with fixed preconditioner $H_0$, the search directions are mutually $A$-conjugate: $d_p^T (A d_q) = 0$ whenever $p \ne q$
-- statement:
--   Along the preconditioned conjugate gradient method with a fixed positive definite preconditioner and exact line searches, the search directions are mutually A-conjugate: the A-inner product of any two distinct directions vanishes.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13): the classical A-conjugacy of the conjugate-gradient directions

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with the
fixed preconditioner `H0`, the search directions are mutually `A`-conjugate:

    d_p ᵀ (A *ᵥ d_q) = 0    whenever    p ≠ q,

where `d_k = (pcgIter A b H₀ x₀ k).d`.

**Why this is the one missing theorem.** Every other relation in this cluster follows from
this one together with the exact line search. Writing `g_k = grad A b (pcgIter A b H₀ x₀ k).x`:

* the gradient/direction orthogonality `g_i ᵀ d_j = 0` for `j < i` is a strong induction on
  `i`, because the gradient is affine along the step,
  `g_{k+1} - g_k = a_k (A *ᵥ d_k)`, so the new term is `a_k d_k ᵀ (A *ᵥ d_j)`, which is
  this theorem at the pair `(k, j)`; the base `g_1 ᵀ d_0 = 0` is the exact line search;
* the gradient orthogonality `g_i ᵀ (H₀ *ᵥ g_j) = 0` for `j < i` then follows from the
  *form* of the direction recurrence `H₀ *ᵥ g_j = -(d_j) + β_{j-1} • d_{j-1}`, since both
  `g_i ᵀ d_j` and `g_i ᵀ d_{j-1}` then vanish. The coefficient `β_{j-1}` is multiplied by an
  exact zero, so neither its numerator nor its denominator is used, there is no division by
  `y_j ᵀ d_j`, and no degenerate case is reached;
* the remaining ordering `j > i` follows from the symmetry of `H₀`.

Only the gap-one case is already available, as the proved child
`pcg_direction_A_conjugacy_step_pd`. The present statement is the full-index version, and it is
the only genuinely new input. -/
theorem pcg_direction_A_conjugacy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ p q : ℕ, p ≠ q →
      (pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ q).d) = 0 := by sorry

end LimitedBFGS.SQN
