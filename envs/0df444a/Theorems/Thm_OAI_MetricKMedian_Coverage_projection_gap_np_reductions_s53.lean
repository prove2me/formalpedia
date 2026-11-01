-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Coverage_projection_gap_np_reductions_s53
-- name    : OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:46:21.526242+00:00
-- url     : https://prove2.me/theorems/d8b76479-c4c8-420e-b42a-c4183e870c27
-- title:
--   OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Coverage.projection_gap_np_reductions` of [lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Coverage`, with `open Complexity PCP PCP.Compiler`, `open scoped Classical`):
--
--   ```lean
--   theorem projection_gap_np_reductions_s53 : ProjectionGapNPReductions
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.ProjectionGapNPReductions` (definitions bundle `OAIQ053K070` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.below_threshold_impossible_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean (declaration OAI.MetricKMedian.Coverage.projection_gap_np_reductions)

import Mathlib
import Definitions.Def_OAIQ053K070

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUniformProjection
namespace MetricKMedian.Coverage
open Complexity PCP PCP.Compiler
open scoped Classical

theorem projection_gap_np_reductions_s53 : ProjectionGapNPReductions := by
  sorry
end MetricKMedian.Coverage

end Inline_PCPUniformProjection

end OAI
end
