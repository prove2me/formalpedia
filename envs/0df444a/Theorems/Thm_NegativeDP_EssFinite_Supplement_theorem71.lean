-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem71
-- name    : NegativeDP.EssFinite.Supplement.theorem71
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:00:57.96182+00:00
-- url     : https://prove2.me/theorems/e73d9e7f-73a5-4b61-abb0-23299ee29d4c
-- title:
--   Theorem 7.1 (D, P) — the optimal return v* is absolutely measurable
-- statement:
--   In the discounted and in the positive bounded case the optimal return $v^*=\sup_\pi I(\pi)$, the supremum over all policies, is **absolutely measurable**: for every probability $p$ on $S$ it is measurable with respect to the completion of $p$,
--
--   $$
--   v^*\in\bigcap_{p\in P(S)}\overline{\mathcal B(S)}^{\,p}\text{-measurable functions}.
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.OptEq.theorem71`; together with this item it covers the whole source theorem. Absolute measurability is what makes $(p,\varepsilon)$-optimality and $T_av^*$ meaningful in §8.
--
--   **Formalization Note** Absolute measurability is `NullMeasurable v* p` for every probability measure `p`. $v^*$ is Blackwell's `optReturn` in case D and `Pos.optReturn` in case P, a real `⨆` over all randomized history-dependent plans.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem71; reason: the negative case is already published and immutable; the two items together state the whole theorem
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 884, Theorem 7.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 7.1 (p. 884), discounted case (first conjunct) and positive bounded case (second
conjunct): `v* = sup_π I(π)` is absolutely measurable, i.e. measurable for the completion of
every probability `p` on `S`. The negative case is the published `NegativeDP.OptEq.theorem71`. -/
theorem theorem71 :
    (∀ (P : Problem S A) (p : Measure S), IsProbabilityMeasure p →
      NullMeasurable (optReturn P) p) ∧
    (∀ (P : Pos.Problem S A) (p : Measure S), IsProbabilityMeasure p →
      NullMeasurable (Pos.optReturn P) p) := by sorry

end NegativeDP.EssFinite.Supplement
