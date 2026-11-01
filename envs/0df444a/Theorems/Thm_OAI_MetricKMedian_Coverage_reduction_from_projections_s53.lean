-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Coverage_reduction_from_projections_s53
-- name    : OAI.MetricKMedian.Coverage.reduction_from_projections_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:45:45.792035+00:00
-- url     : https://prove2.me/theorems/d5726604-c4b7-495f-b5fb-e3319a0e3a22
-- title:
--   OAI.MetricKMedian.Coverage.reduction_from_projections_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Coverage.reduction_from_projections` of [lean/OAI/Combinatorics/KMedian/Hardness/ProjectionReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/ProjectionReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Coverage`, with `open Complexity`):
--
--   ```lean
--   theorem reduction_from_projections_s53 {δ : ℝ} (P : PartitionParameters δ)
--       {L : Language} (h : ProjectionReduction P.ε L) :
--       ∃ reduce : Word → Input, FinitePolyTime id Input.encode reduce ∧
--         (∀ x, x ∈ L → (reduce x).Perfect) ∧
--         (∀ x, x ∉ L → (reduce x).Sound δ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.Input`, `OAI.MetricKMedian.Coverage.PartitionParameters`, `OAI.MetricKMedian.Coverage.Input.Perfect`, `OAI.MetricKMedian.Coverage.Input.Sound` and `OAI.MetricKMedian.Coverage.Input.encode` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.Coverage.ProjectionReduction` (definitions bundle `OAIQ053K070` of this split); `OAI.MetricKMedian.Complexity.FinitePolyTime`, `OAI.MetricKMedian.Complexity.Language` and `OAI.MetricKMedian.Complexity.Word` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.below_threshold_impossible_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/ProjectionReduction.lean (declaration OAI.MetricKMedian.Coverage.reduction_from_projections)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

theorem reduction_from_projections_s53 {δ : ℝ} (P : PartitionParameters δ)
    {L : Language} (h : ProjectionReduction P.ε L) :
    ∃ reduce : Word → Input, FinitePolyTime id Input.encode reduce ∧
      (∀ x, x ∈ L → (reduce x).Perfect) ∧
      (∀ x, x ∉ L → (reduce x).Sound δ) := by
  sorry

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end
