-- Prove2me | Theorems.Thm_OAI_SLEExactGauge_source_mesh_parameters
-- name    : OAI.SLEExactGauge.source_mesh_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:38:24.345999+00:00
-- url     : https://prove2.me/theorems/d84f26e8-d2ed-48b6-9657-5ec4e13a2dec
-- title:
--   OAI.SLEExactGauge.source_mesh_parameters: intermediate lemma from OpenAI, An explicit exact Hausdorff gauge for SLE
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SLEExactGauge.sourceLowerMain_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit exact Hausdorff gauge for SLE*, OpenAI Math Release, September 26, 2026, result family 230, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SLEExactGauge.source_mesh_parameters` of [lean/OAI/Probability/SLE/PhysicalMeshPast.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/PhysicalMeshPast.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SLEExactGauge`, with `open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   lemma source_mesh_parameters (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
--       Nonempty (SourceMeshParameters κ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SLEExactGauge.SourceMeshParameters` (definitions bundle `OAIQ27Sle000` of this split).
--
--   **Used by.** The proofs of `OAI.SLEExactGauge.RegularSLEPresentation.source_actual_retained_experiment_allKappa` and `OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa` of this split import it.
-- source:
--   OpenAI, An explicit exact Hausdorff gauge for SLE, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 230; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/PhysicalMeshPast.lean (declaration OAI.SLEExactGauge.source_mesh_parameters)

import Mathlib
import Definitions.Def_OAIQ27Sle000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_parameters (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    Nonempty (SourceMeshParameters κ) := by
  sorry

end
end SLEExactGauge
end

end OAI
end
