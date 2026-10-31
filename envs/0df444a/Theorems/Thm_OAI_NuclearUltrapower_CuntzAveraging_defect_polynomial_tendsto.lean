-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_polynomial_tendsto
-- name    : OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:42.270116+00:00
-- url     : https://prove2.me/theorems/efad2caa-5149-4ad7-9bf0-14eb1c23b845
-- title:
--   OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto` of [lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.CuntzAveraging`, with `open Filter`, `open scoped Topology TensorProduct`, `open CuntzUniversal`):
--
--   ```lean
--   theorem defect_polynomial_tendsto (p : CuntzPolynomial.Poly) :
--       Tendsto (fun n => defect R n (inclusion p)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.CuntzAveraging.Target`, `OAI.NuclearUltrapower.CuntzModel.Index`, `OAI.NuclearUltrapower.CuntzModel.Space`, `OAI.NuclearUltrapower.CuntzPolynomial.Letter`, `OAI.NuclearUltrapower.CuntzPolynomial.Poly` and `OAI.NuclearUltrapower.CuntzPolynomial.Word` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace`, `OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly`, `OAI.NuclearUltrapower.CuntzUniversal.Algebra`, `OAI.NuclearUltrapower.CuntzUniversal.inclusion` and `OAI.NuclearUltrapower.CuntzUniversal.instCStarAlgebraAlgebra` (definitions bundle `OAIQ019N039` of this split); `OAI.NuclearUltrapower.CuntzAveraging.defect` (definitions bundle `OAIQ019N042` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean (declaration OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto)

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

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace_1_rad82b0_1 : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget_1
theorem defect_polynomial_tendsto (p : CuntzPolynomial.Poly) :
    Tendsto (fun n => defect R n (inclusion p)) atTop (𝓝 0) := by
  sorry

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end
