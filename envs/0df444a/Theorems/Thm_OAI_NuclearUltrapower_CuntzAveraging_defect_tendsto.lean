-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_tendsto
-- name    : OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:01:15.836342+00:00
-- url     : https://prove2.me/theorems/a91e35b9-c660-4b71-a32f-0c179f2a02d1
-- title:
--   OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto` of [lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.CuntzAveraging`, with `open Filter`, `open scoped Topology TensorProduct`, `open CuntzUniversal`):
--
--   ```lean
--   theorem defect_tendsto (a : Algebra) :
--       Tendsto (fun n => defect R n a) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.CuntzAveraging.Target`, `OAI.NuclearUltrapower.CuntzModel.Index` and `OAI.NuclearUltrapower.CuntzModel.Space` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace`, `OAI.NuclearUltrapower.CuntzUniversal.Algebra` and `OAI.NuclearUltrapower.CuntzUniversal.instCStarAlgebraAlgebra` (definitions bundle `OAIQ019N039` of this split); `OAI.NuclearUltrapower.CuntzAveraging.defect` (definitions bundle `OAIQ019N042` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.CuntzAveraging.jointDefect_tendsto` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean (declaration OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto)

import Mathlib
import Definitions.Def_OAIQ019N042

section

attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology TensorProduct
namespace NuclearUltrapower.CuntzAveraging
open CuntzUniversal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace_1_r63f3ad_1 : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget_1
theorem defect_tendsto (a : Algebra) :
    Tendsto (fun n => defect R n a) atTop (𝓝 0) := by
  sorry

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end
