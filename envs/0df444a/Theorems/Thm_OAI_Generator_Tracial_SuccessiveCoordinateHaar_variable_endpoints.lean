-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_variable_endpoints
-- name    : OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T11:08:43.865183+00:00
-- url     : https://prove2.me/theorems/4e3e2ff4-5675-4d6a-9a59-99a8f0112088
-- title:
--   OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints` of [lean/OAI/Analysis/FactorGeneration/HaarSequences.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem SuccessiveCoordinateHaar.variable_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
--       (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (j : ℕ) :
--       HaarEndpoints τ ω (F.algebra j).toSubalgebra
--         (prefixVariable τ ω u (fun k => (F.step k).t) j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ11Fg000` of this split); `OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient` and `OAI.UltrapowerBridge.instStarRingTracialQuotient` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.SuccessiveCoordinateHaar` (definitions bundle `OAIQ11Fg015` of this split); `OAI.Generator.Tracial.HaarEndpoints` and `OAI.Generator.Tracial.CoordinateHaarData` (definitions bundle `OAIQ11Fg020` of this split); `OAI.Generator.Tracial.prefixVariable` (definitions bundle `OAIQ11Fg022` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_negative_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_positive_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.conjugate_trace`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_freeGroup_trace`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation`, `OAI_Generator_Tracial_SuccessiveCoordinateHaar_prefix_endpoints` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.target_endpoints` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean (declaration OAI.Generator.Tracial.SuccessiveCoordinateHaar.variable_endpoints)

import Mathlib
import Definitions.Def_OAIQ11Fg022

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.variable_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (j : ℕ) :
    HaarEndpoints τ ω (F.algebra j).toSubalgebra
      (prefixVariable τ ω u (fun k => (F.step k).t) j) := by
  sorry

end Generator.Tracial

end

end OAI
end
