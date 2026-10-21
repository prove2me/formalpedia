-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_step_3
-- name    : InterimRatImpl.Sufficiency.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:34.653816+00:00
-- url     : https://prove2.me/theorems/a8a1688b-16d5-48c9-9c40-432736a968a1
-- title:
--   Step 3 — truthful level-one messages are rationalizable
-- statement:
--   Let $S_i(t_i)$ contain the canonical messages with level one and self-report $t_i$. Under Bayesian incentive compatibility, $S$ is post-fixed by the best-response operator, lies below the greatest fixed point, and has a message for every type:
--
--   $$
--   S\le b(S),\qquad S\le S^\Gamma(T),\qquad S_i(t_i)\ne\varnothing.
--   $$
--
--   This supplies the nonemptiness part of implementation.
--
--   **Formalization Note** The proof of this step needs BIC; the paper obtains it from weak IRM via Lemma 5.2. The canonical construction is stated for at least two agents.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 27 (PDF 28), Step 3

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Step 3 of Theorem 6.3: truthful level-one messages are post-fixed,
hence rationalizable; every type has such a message. -/
theorem step_3 (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) (hcard : 2 ≤ Fintype.card I)
    (hBIC : BIC E fhat) :
    truthMessages E fhat P ≤ b E (canonG E fhat P) (truthMessages E fhat P) ∧
    truthMessages E fhat P ≤ SGamma E (canonG E fhat P) ∧
    (∀ i ti, (truthMessages E fhat P i ti).Nonempty) := by sorry

end InterimRatImpl.Sufficiency
