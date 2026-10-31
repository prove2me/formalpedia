-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_predualFunctional_mem_cyclicPredual
-- name    : OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:48:45.660315+00:00
-- url     : https://prove2.me/theorems/2b8628d9-51c5-46b3-9649-ba63418f1428
-- title:
--   OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual` of [lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem predualFunctional_mem_cyclicPredual (x : X) :
--       predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.predualFunctional` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.cyclicPredual` (definitions bundle `OAIQ11Fg009` of this split).
--
--   **Used by.** The proof of `OAI.Generator.single_generation_of_II1_separable_predual` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean (declaration OAI.Generator.Tracial.predualFunctional_mem_cyclicPredual)

import Mathlib
import Definitions.Def_OAIQ11Fg009

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

theorem predualFunctional_mem_cyclicPredual (x : X) :
    predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ := by
  sorry

end Generator.Tracial

end

end OAI
end
