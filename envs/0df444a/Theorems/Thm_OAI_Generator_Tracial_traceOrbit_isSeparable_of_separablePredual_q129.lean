-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual_q129
-- name    : OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:41:49.236019+00:00
-- url     : https://prove2.me/theorems/0fa8f937-8bd2-4969-9c13-eb1497d0f40d
-- title:
--   OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual` of [lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem traceOrbit_isSeparable_of_separablePredual_q129
--       (hsep : HasSeparablePredual M.toStarSubalgebra) :
--       TopologicalSpace.IsSeparable (Set.range (baseVector τ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.HasSeparablePredual` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proofs of `OAI.Generator.single_generation_of_II1_separable_predual` and `OAI.RelativeGeneration.main_theorem` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean (declaration OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G008

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

theorem traceOrbit_isSeparable_of_separablePredual_q129
    (hsep : HasSeparablePredual M.toStarSubalgebra) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  sorry

end Generator.Tracial

end

end OAI
end
