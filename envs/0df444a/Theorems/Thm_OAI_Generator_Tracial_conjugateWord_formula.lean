-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_conjugateWord_formula
-- name    : OAI.Generator.Tracial.conjugateWord_formula
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T13:08:50.367113+00:00
-- url     : https://prove2.me/theorems/c11acac3-4319-41cc-8ccd-59e88727a7bd
-- title:
--   OAI.Generator.Tracial.conjugateWord_formula: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.conjugateWord_formula` of [lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem conjugateWord_formula (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
--       (a : A × Bool) (w : List (A × Bool)) :
--       unitaryWord τ ω (conjugateVariables τ ω p y) (a::w)=
--         (p a.1 : Q τ ω)*betweenWord (y : Q τ ω) (!a.2)
--           (conjugateGaps τ ω p a w) (conjugateEnd τ ω p a w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.betweenWord` (definitions bundle `OAIQ11Fg002` of this split); `OAI.UltrapowerBridge.instStarRingTracialQuotient` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.conjugateEnd` and `OAI.Generator.Tracial.conjugateGaps` (definitions bundle `OAIQ11Fg016` of this split); `OAI.Generator.Tracial.conjugateVariables` (definitions bundle `OAIQ11Fg022` of this split); `OAI.Generator.Tracial.unitaryWord` (definitions bundle `OAIQ11Fg023` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_sq`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap_gram` and `OAI_Generator_Tracial_conjugate_reduced_word_zero` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean (declaration OAI.Generator.Tracial.conjugateWord_formula)

import Mathlib
import Definitions.Def_OAIQ11Fg022
import Definitions.Def_OAIQ11Fg023

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

section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

theorem conjugateWord_formula (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω (conjugateVariables τ ω p y) (a::w)=
      (p a.1 : Q τ ω)*betweenWord (y : Q τ ω) (!a.2)
        (conjugateGaps τ ω p a w) (conjugateEnd τ ω p a w) := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
