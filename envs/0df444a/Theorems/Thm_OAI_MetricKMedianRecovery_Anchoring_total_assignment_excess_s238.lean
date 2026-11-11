-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Anchoring_total_assignment_excess_s238
-- name    : OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:34.928633+00:00
-- url     : https://prove2.me/theorems/4cbb04c6-0bbf-41bb-9d98-3d89b6190f23
-- title:
--   OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Anchoring`, with `open MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   lemma total_assignment_excess_s238 (F D O S G : Finset V) (hS : S.Nonempty)
--       (hSF : S ⊆ F) (hOF : O ⊆ F) (hGO : G ⊆ O)
--       (hlocal : WidthLocalMin F D S 5) (assign : V → V)
--       (hassign : ∀ p ∈ D, assign p ∈ O) (b t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
--       (hwt : ∀ i ∈ G, clusterWeight D S assign i ≤ t*b)
--       (hr : ∀ i ∈ G, dist i (nearest S hS i) ≤ t*separation O i)
--       (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
--       (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
--         t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ)+
--         (4*t+t/(1-t))*(∑ p ∈ D, (connection S p+dist p (assign p)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.ballFacilities`, `OAI.MetricKMedianRecovery.Anchoring.cluster`, `OAI.MetricKMedianRecovery.Anchoring.clusterWeight`, `OAI.MetricKMedianRecovery.Anchoring.separation`, `OAI.MetricKMedianRecovery.LocalSearch.connection` and `OAI.MetricKMedianRecovery.LocalSearch.nearest` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/TotalAssignmentExcess.lean (declaration OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess)

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

lemma total_assignment_excess_s238 (F D O S G : Finset V) (hS : S.Nonempty)
    (hSF : S ⊆ F) (hOF : O ⊆ F) (hGO : G ⊆ O)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) (b t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hwt : ∀ i ∈ G, clusterWeight D S assign i ≤ t*b)
    (hr : ∀ i ∈ G, dist i (nearest S hS i) ≤ t*separation O i)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ)+
      (4*t+t/(1-t))*(∑ p ∈ D, (connection S p+dist p (assign p))) := by
  sorry

end MetricKMedianRecovery.Anchoring

end OAI
end
