-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Surplus_protected_partition_cost_s238
-- name    : OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:58.086192+00:00
-- url     : https://prove2.me/theorems/3b83aec9-9da1-4243-a3c7-c1c0bc3a3fb8
-- title:
--   OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/ClusterCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/ClusterCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Surplus`, with `open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring`):
--
--   ```lean
--   lemma protected_partition_cost_s238 (F D S O G B : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
--       (hSF : S ⊆ F) (hOF : O ⊆ F) (hlocal : WidthLocalMin F D S 5)
--       (hcard : O.card ≤ S.card) (hpart : G ∪ B = O) (hdis : Disjoint G B)
--       (hinj : Set.InjOn (nearest S hS) G) :
--       cost D S ≤ (17/5:ℝ)*partCost D B (nearest O hO)+
--         (6/5:ℝ)*partCharge D G (nearest O hO) (nearest S hS)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.LocalSearch.nearest` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Surplus.partCharge` and `OAI.MetricKMedianRecovery.Surplus.partCost` (definitions bundle `Q238K016` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/ClusterCost.lean (declaration OAI.MetricKMedianRecovery.Surplus.protected_partition_cost)

import Mathlib
import Definitions.Def_Q238K015
import Definitions.Def_Q238K016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma protected_partition_cost_s238 (F D S O G B : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hOF : O ⊆ F) (hlocal : WidthLocalMin F D S 5)
    (hcard : O.card ≤ S.card) (hpart : G ∪ B = O) (hdis : Disjoint G B)
    (hinj : Set.InjOn (nearest S hS) G) :
    cost D S ≤ (17/5:ℝ)*partCost D B (nearest O hO)+
      (6/5:ℝ)*partCharge D G (nearest O hO) (nearest S hS) := by
  sorry

end MetricKMedianRecovery.Surplus

end OAI
end
