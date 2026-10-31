-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_defect_generator_bound
-- name    : OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:07.610337+00:00
-- url     : https://prove2.me/theorems/fd57e46e-b871-4e92-8bf5-f9cf13901578
-- title:
--   OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound` of [lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.CuntzAveraging`, with `open Filter`, `open scoped TensorProduct InnerProductSpace Topology`, `open CuntzModel CuntzWords CuntzUniversal`):
--
--   ```lean
--   theorem defect_generator_bound (n : ℕ) (i : Fin 2) :
--       ‖defect R n (generator i)‖ ≤ ((n : ℝ)+1)⁻¹ * 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.CuntzAveraging.Target`, `OAI.NuclearUltrapower.CuntzModel.Index` and `OAI.NuclearUltrapower.CuntzModel.Space` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace`, `OAI.NuclearUltrapower.CuntzUniversal.Algebra`, `OAI.NuclearUltrapower.CuntzUniversal.generator` and `OAI.NuclearUltrapower.CuntzUniversal.instCStarAlgebraAlgebra` (definitions bundle `OAIQ019N039` of this split); `OAI.NuclearUltrapower.CuntzAveraging.defect` and `OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget` (definitions bundle `OAIQ019N042` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean (declaration OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound)

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
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget
theorem defect_generator_bound (n : ℕ) (i : Fin 2) :
    ‖defect R n (generator i)‖ ≤ ((n : ℝ)+1)⁻¹ * 2 := by
  sorry

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end
