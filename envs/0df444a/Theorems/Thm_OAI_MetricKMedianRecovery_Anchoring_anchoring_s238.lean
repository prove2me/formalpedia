-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Anchoring_anchoring_s238
-- name    : OAI.MetricKMedianRecovery.Anchoring.anchoring_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:17:06.447077+00:00
-- url     : https://prove2.me/theorems/b4ba2bdc-749c-4560-8b73-3f3ff93a2a3e
-- title:
--   OAI.MetricKMedianRecovery.Anchoring.anchoring_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Anchoring.anchoring` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Anchoring`, with `open MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   theorem anchoring_s238 (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
--       (hO2 : 2 ≤ O.card) (hSF : S ⊆ F) (hOF : O ⊆ F)
--       (hcard : O.card ≤ S.card) (hlocal : WidthLocalMin F D S 5)
--       (b mu : ℝ) (hb : 0 < b) (hP : 0 < cost D O) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
--       (hscale : b*((S.card:ℝ)-O.card+
--         (shortCenters O (clusterScale D O (nearest O hO)) b).card) ≤ 10*cost D O) :
--       ∃ G B : Finset V,
--         G ∪ B = O ∧ Disjoint G B ∧
--         Set.InjOn (nearest S hS) G ∧
--         (∀ i ∈ G, nearest S hS i ∈ S) ∧
--         (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p (nearest S hS i)) ≤
--           (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p i)+mu*cost D O ∧
--         (B.card:ℝ) ≤ countConstant mu*cost D O/b
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.cluster`, `OAI.MetricKMedianRecovery.Anchoring.clusterScale`, `OAI.MetricKMedianRecovery.Anchoring.countConstant`, `OAI.MetricKMedianRecovery.Anchoring.shortCenters` and `OAI.MetricKMedianRecovery.LocalSearch.nearest` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238` and `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean (declaration OAI.MetricKMedianRecovery.Anchoring.anchoring)

import Mathlib
import Definitions.Def_Q238K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem anchoring_s238 (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hSF : S ⊆ F) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) (hlocal : WidthLocalMin F D S 5)
    (b mu : ℝ) (hb : 0 < b) (hP : 0 < cost D O) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hscale : b*((S.card:ℝ)-O.card+
      (shortCenters O (clusterScale D O (nearest O hO)) b).card) ≤ 10*cost D O) :
    ∃ G B : Finset V,
      G ∪ B = O ∧ Disjoint G B ∧
      Set.InjOn (nearest S hS) G ∧
      (∀ i ∈ G, nearest S hS i ∈ S) ∧
      (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p (nearest S hS i)) ≤
        (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p i)+mu*cost D O ∧
      (B.card:ℝ) ≤ countConstant mu*cost D O/b := by
  sorry

end MetricKMedianRecovery.Anchoring

end OAI
end
