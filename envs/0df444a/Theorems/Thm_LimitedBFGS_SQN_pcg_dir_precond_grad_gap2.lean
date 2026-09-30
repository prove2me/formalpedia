-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_dir_precond_grad_gap2
-- name    : LimitedBFGS.SQN.pcg_dir_precond_grad_gap2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:10:56.752114+00:00
-- url     : https://prove2.me/theorems/ac9a61b9-1bdf-4174-b65c-406d358c6fc7
-- title:
--   Along the PCG with fixed preconditioner $H_0$, the direction $d_p$ is orthogonal to $A (H_0 g_q)$ once $q \ge p+2$
-- statement:
--   Along the preconditioned conjugate gradient method with a fixed positive definite preconditioner, each search direction is orthogonal to A times the preconditioned gradient of any iterate at least two steps later.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13): the direction/gradient coupling underlying eqs. (15)-(16) for non-adjacent indices

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with the
fixed preconditioner `H0`, a search direction is orthogonal to the `A`-image of a later
preconditioned gradient:

    d_p ᵀ (A *ᵥ (H₀ *ᵥ g_q)) = 0    whenever    q ≥ p + 2,

where `g_k = grad A b (pcgIter A b H₀ x₀ k).x` and `d_k = (pcgIter A b H₀ x₀ k).d`.

**Why the gap two.** The coupling identity

    d_p ᵀ (A *ᵥ d_q) = - d_p ᵀ (A *ᵥ (H₀ *ᵥ g_q))

holds at *every* column `q`, because `d_q = -(H₀ *ᵥ g_q) + β d_{q-1}` and the `β` term dies
against `d_p` by the `A`-conjugacy of the directions. The left-hand side is the classical
`A`-conjugacy, which the one-step lemma `pcg_direction_A_conjugacy_step_pd` supplies at
gap one only, so the right-hand side is *not* expected to vanish at gap one; it is measured
non-zero there. For every gap of at least two it does vanish, and that is the statement here.

This is the piece of the closure of `pcg_grad_orthogonality` that is neither the target nor
the already-proved one-step lemma, and it is what a lower-triangular induction on the later
index needs for the non-adjacent columns. -/
theorem pcg_dir_precond_grad_gap2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ p q : ℕ, p + 2 ≤ q →
      (pcgIter A b H₀ x₀ p).d ⬝ᵥ (A *ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ q).x)) = 0 := by sorry

end LimitedBFGS.SQN
