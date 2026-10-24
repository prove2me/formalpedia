-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_7_1
-- name    : OnlineMaxWeightMatch.Approx.proposition_2_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:42.23215+00:00
-- url     : https://prove2.me/theorems/5759c628-fac0-447f-a9db-74308cbe15de
-- title:
--   Proposition 2.7.1 (NA closure under independent union)
-- statement:
--   Let $(X_1,\dots,X_n)$ and $(Y_1,\dots,Y_m)$ be two negatively associated families of random variables on the same probability space, and suppose the two random vectors $(X_1,\dots,X_n)$ and $(Y_1,\dots,Y_m)$ are mutually independent. Then the joint family
--
--   $$
--   (X_1,\dots,X_n,Y_1,\dots,Y_m)
--   $$
--
--   is negatively associated.
--
--   In the proof of Lemma 4.9 this closure property combines the pick indicators and the acceptance coins of one ball, and then the families of different balls, into one NA family.
--
--   **Formalization Note** "Mutually independent" is independence of the two vector-valued random variables (`IndepFun`), not coordinatewise independence. The variables are measurable and the measure is a probability measure. The joint family is indexed by the disjoint union of the two index sets.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, Proposition 2.7, part 1

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Proposition 2.7.1 (independent union). If `(X_1, …, X_n)` and `(Y_1, …, Y_m)` are negatively
associated and mutually independent (as random vectors), then the joint family
`(X_1, …, X_n, Y_1, …, Y_m)` is negatively associated. -/
theorem proposition_2_7_1 {Ω κ₁ κ₂ : Type*} [MeasurableSpace Ω] [Fintype κ₁] [Fintype κ₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : κ₁ → Ω → ℝ) (Y : κ₂ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hindep : IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) μ)
    (hXNA : NegativelyAssociated X μ) (hYNA : NegativelyAssociated Y μ) :
    NegativelyAssociated (Sum.elim X Y) μ := by sorry

end OnlineMaxWeightMatch.Approx
