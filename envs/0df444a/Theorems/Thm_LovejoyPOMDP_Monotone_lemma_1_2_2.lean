-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_2_2
-- name    : LovejoyPOMDP.Monotone.lemma_1_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:46.25376+00:00
-- url     : https://prove2.me/theorems/afe48d9a-4828-42c2-b3e7-00c7a6ca5f14
-- title:
--   Lemma 1.2, part 2 — T(π, a, k) is MLR-monotone in π iff πP^a is
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with $r^a_{jk}>0$ for all $j,k,a$. For every action $a\in A$ and observation $k\in O$, the following are equivalent:
--
--   1. $T(\pi,a,k)\ge_r T(\pi',a,k)$ for all $\pi\ge_r\pi'$ in $\Pi(S)$;
--   2. $\pi P^a\ge_r\pi' P^a$ for all $\pi\ge_r\pi'$ in $\Pi(S)$.
--
--   The Bayes update preserves the MLR order of priors exactly when the prediction step does. Together with Lemma 1.3(1) this gives the monotonicity of the posterior in the prior used in Proposition 1.
--
--   **Formalization Note** The equivalence relies on the standing assumption $r^a_{jk}>0$ (a field of the model), which makes $\sigma(k;\pi,a)>0$ on $\Pi(S)$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, pp. 738–739, Lemma 1.2, part 2

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, pp. 738–739, Lemma 1.2, part 2.

For any `a ∈ A` and `k ∈ O`: `T(π, a, k) ≥r T(π', a, k)` for all `π ≥r π'` in `Π(S)` if and only
if `πP^a ≥r π'P^a` for all `π ≥r π'` in `Π(S)`.

**Formalization Note.** The equivalence uses the standing assumption `r^a_{jk} > 0`, which is a
field of `POMDP`. -/
theorem lemma_1_2_2 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A) (a : A) (k : O) :
    (∀ π π' : S → ℝ, π ∈ stdSimplex ℝ S → π' ∈ stdSimplex ℝ S → MLRGE π π' →
        MLRGE (M.bayes π a k) (M.bayes π' a k)) ↔
      (∀ π π' : S → ℝ, π ∈ stdSimplex ℝ S → π' ∈ stdSimplex ℝ S → MLRGE π π' →
        MLRGE (M.predict π a) (M.predict π' a)) := by sorry

end LovejoyPOMDP.Monotone
