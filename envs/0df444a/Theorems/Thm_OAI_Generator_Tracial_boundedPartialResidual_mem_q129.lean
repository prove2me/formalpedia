-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_boundedPartialResidual_mem_q129
-- name    : OAI.Generator.Tracial.boundedPartialResidual_mem_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:50:10.856335+00:00
-- url     : https://prove2.me/theorems/7549b9a4-d808-4ec9-8504-9df3c64fe5af
-- title:
--   OAI.Generator.Tracial.boundedPartialResidual_mem_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.boundedPartialResidual_mem` of [lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem boundedPartialResidual_mem_q129 (v : ℕ → PartialUnitary M)
--       (hv : ∀ j,(v j).val.val ∈ N) (j : ℕ) :
--       ((boundedPartialResidual v).val j).val ∈ N
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.PartialUnitary` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ129G005` of this split); `OAI.Generator.Tracial.boundedPartialResidual` (definitions bundle `OAIQ129G012` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_exact_residual_iteration_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean (declaration OAI.Generator.Tracial.boundedPartialResidual_mem)

import Mathlib
import Definitions.Def_OAIQ129G012

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem boundedPartialResidual_mem_q129 (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) (j : ℕ) :
    ((boundedPartialResidual v).val j).val ∈ N := by
  sorry

end

open Filter

open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end
