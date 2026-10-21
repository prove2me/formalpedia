-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_lemma_5_2
-- name    : InterimRatImpl.Sufficiency.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:34.201979+00:00
-- url     : https://prove2.me/theorems/e2161dd7-44d3-4711-b881-7ba41953ff54
-- title:
--   Lemma 5.2 — weak IRM implies SIRBIC
-- statement:
--   If a social choice function $f:T\to\Delta(A)$ satisfies weak interim rationalizable monotonicity, then it is Bayesian incentive compatible, with a strict incentive whenever changing agent $i$'s reported type changes some outcome of $f$:
--
--   $$
--   U_i(f;t_i'\mid t_i)\le U_i(f\mid t_i),\qquad
--    t_i\not\sim_i^f t_i'\Longrightarrow U_i(f;t_i'\mid t_i)<U_i(f\mid t_i).
--   $$
--
--   This connects the paper's deception criterion to the direct-report incentive constraints used in the implementation proof.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 15 (PDF 16), Lemma 5.2

import Definitions.Def_InterimRatImpl_Sufficiency_Model

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Lemma 5.2, p. 15: weak IRM entails strict-if-responsive BIC. -/
theorem lemma_5_2 (E : Env I T A) (f : SCF T A) (h : WeakIRM E f) :
    SIRBIC E f := by sorry

end InterimRatImpl.Sufficiency
