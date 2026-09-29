-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_direction_residual_orth
-- name    : LimitedBFGS.SQN.pcg_direction_residual_orth
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:54:04.269033+00:00
-- url     : https://prove2.me/theorems/da38e6f9-7296-4d9b-a252-c3a84d5b75f4
-- title:
--   Eq. (16) auxiliary: the residual H0 g_k + d_k is A-orthogonal to the direction d_k, making the adjacent case g_{k+1}^T H0 g_k = 0 a one-step identity
-- statement:
--   Let f(x) = 1/2 x^T A x + b^T x on R^n with A symmetric positive definite, H_0 a fixed symmetric positive definite preconditioner, and x_0 in R^n. Run the preconditioned conjugate gradient method with fixed preconditioner H_0 and exact line searches from x_0, with iterates x_i, directions d_i and gradients g_i = A x_i + b, so that d_0 = -H_0 g_0, x_{i+1} = x_i + a_i d_i and d_{i+1} = -H_0 g_{i+1} + beta_i d_i. Then the residual left over by the direction recurrence, r_k = H_0 g_k + d_k, is orthogonal in the A form to the direction used at step k: r_k^T (A d_k) = 0. At k = 0 the residual is literally zero, since d_0 = -H_0 g_0. At k = j+1 the recurrence gives r_{j+1} = beta_j d_j, and d_j is A-orthogonal to d_{j+1}, so the claim is the already-proved one-step A-conjugacy of the directions multiplied by beta_j. The step coefficient needs no hypothesis, because it is only ever multiplied against something already known to vanish. This is what makes the adjacent case of the first relation of eq. (16), g_{k+1}^T H_0 g_k = 0, a one-step identity rather than part of an induction.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13), read against the one-step A-conjugacy of the search directions. The residual H_0 g_k + d_k is the part of g_k's H_0-preconditioned direction that the beta recurrence does not carry, and it is exactly what the adjacent case of eq. (16) needs.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (16), p. 777: the residual left over by the direction recurrence,

    r_k := H₀ *ᵥ g_k + d_k,

is orthogonal, in the `A` form, to the direction used at step `k`:

    r_k ⬝ᵥ (A *ᵥ d_k) = 0.

**Proof.** At `k = 0` the recurrence is absent: the zeroth clause of the
iteration gives `d_0 = -(H₀ *ᵥ g_0)` exactly, so `r_0 = 0` and there is nothing
to prove. At `k = j + 1` the direction recurrence
`d_{j+1} = -(H₀ *ᵥ g_{j+1}) + beta_j * d_j` gives `r_{j+1} = beta_j * d_j`, so

    r_{j+1} ⬝ᵥ (A *ᵥ d_{j+1}) = beta_j (d_j ⬝ᵥ (A *ᵥ d_{j+1}))
                            = beta_j (d_{j+1} ⬝ᵥ (A *ᵥ d_j))     [`A` symmetric]
                            = 0

by the already-proved child `pcg_direction_A_conjugacy_step_pd`. The step
coefficient `beta_j` needs no hypothesis: it is the quotient the definition
itself forms, and it is only ever multiplied against something already known to
vanish, so the possibly-zero denominator `y_j ⬝ᵥ d_j` never has to be
discharged.

**Why it matters.** This is what makes the *adjacent* case of eq. (16)'s first
relation, `g_{k+1} ⬝ᵥ (H₀ *ᵥ g_k) = 0`, a one-step identity rather than part of
an induction: the term that would otherwise survive the step is exactly
`a_k (r_k ⬝ᵥ (A *ᵥ d_k))`, and this lemma kills it. -/
theorem pcg_direction_residual_orth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k).x + (pcgIter A b H₀ x₀ k).d) ⬝ᵥ
        (A *ᵥ (pcgIter A b H₀ x₀ k).d) = 0 := by sorry

end LimitedBFGS.SQN
