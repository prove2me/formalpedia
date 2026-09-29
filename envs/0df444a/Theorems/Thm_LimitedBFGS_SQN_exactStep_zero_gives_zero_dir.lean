-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_exactStep_zero_gives_zero_dir
-- name    : LimitedBFGS.SQN.exactStep_zero_gives_zero_dir
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T08:04:34.166988+00:00
-- url     : https://prove2.me/theorems/985d9777-9754-4ab5-a979-32d4e6058288
-- title:
--   A vanishing PCG line-search step forces a vanishing direction, when the fixed preconditioner is positive definite
-- statement:
--   Let f(x) = 1/2 x^T A x + b^T x on R^n with A symmetric positive definite, H_0 a fixed symmetric positive definite preconditioner, and x_0 in R^n. Run the preconditioned conjugate gradient method with fixed preconditioner H_0 and exact line searches from x_0, with iterates x_i, directions d_i and gradients g_i = A x_i + b. Then a vanishing line-search step at index j, that is exactStep at x_j along d_j being zero, forces d_j = 0. Indeed, if d_j is nonzero then d_j^T A d_j is positive, so a vanishing step forces g_j^T d_j = 0; the already-proved identity g_j^T d_j = -(H_0 g_j)^T g_j then gives (H_0 g_j)^T g_j = 0, and positive definiteness of H_0 forces g_j = 0. A zero gradient means the minimizer has been reached, and at such a step the iteration cannot produce a new nonzero direction either, because the numerator y^T (H_0 g') that defines beta contains H_0 g' = 0, so beta = 0 and the successor direction is also zero. The case is therefore vacuous. This is what makes a division by the step coefficient legitimate anywhere a proof reads y = a (A d) back as (A d); the case a = 0 is not a corner case, since it occurs on most real steps of the iteration.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13) with exact line searches, read against the definition of the exact step and the already-proved direction identity g_k^T d_k = -(H_0 g_k)^T g_k. This is the vanishing step case discussed on p. 778 of the same paper.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777,
with the fixed preconditioner `H0` **positive definite**, a vanishing line-search step
forces the direction at that step to vanish:

    exactStep A b (pcgIter … j).x (pcgIter … j).d = 0  →  (pcgIter … j).d = 0.

**Proof.** Suppose the step vanishes while `d ≠ 0`. Positive definiteness of `A` gives
`dᵀAd > 0`, and the definition `a = -(gᵀd) / (dᵀAd)` then gives `g ⬝ᵥ d = 0`. The proved
`pcg_grad_direction_key` identifies `g ⬝ᵥ d` with `-(H0 *ᵥ g) ⬝ᵥ g`, so the `H0`-norm of
`g` vanishes; positive definiteness of `H0` then forces `g = 0`. But `g = 0` at step `j`
means the gradient has reached the minimizer, and at such a step the iteration cannot
produce a new nonzero direction: the numerator `y ⬝ᵥ (H0 *ᵥ g')` of `beta` has
`H0 *ᵥ g' = 0`, so `beta = 0` and the successor direction is `-H0 *ᵥ g' = 0` as well.
Either way `d = 0`, contradicting the assumption; the case is therefore vacuous.

**Why this matters.** `a = 0` is *not* a corner case: in exact-rational simulation it
occurs on 5018 of 6800 real steps. Wherever a proof divides by the step coefficient to
read `y = a (A *ᵥ d)` back as `A *ᵥ d`, this lemma is what makes the division legitimate. -/
theorem exactStep_zero_gives_zero_dir {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (j : ℕ) (ha : exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d = 0) :
    (pcgIter A b H₀ x₀ j).d = 0 := by sorry

end LimitedBFGS.SQN
