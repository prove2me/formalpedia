-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_nonempty_coordinateHaarData
-- name    : OAI.Generator.Tracial.nonempty_coordinateHaarData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T10:19:56.549752+00:00
-- url     : https://prove2.me/theorems/3d808bf9-f698-4f59-8056-5a76f1ea5126
-- title:
--   OAI.Generator.Tracial.nonempty_coordinateHaarData: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.nonempty_coordinateHaarData` of [lean/OAI/Analysis/FactorGeneration/HaarSequences.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem nonempty_coordinateHaarData (hω : (ω : Filter ℕ) ≤ atTop)
--       (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
--       Nonempty (CoordinateHaarData τ ω hNM D)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.traceCongruence` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.quotientNormedAddCommGroup` (definitions bundle `OAIQ11Fg011` of this split); `OAI.Generator.Tracial.CoordinateHaarData` (definitions bundle `OAIQ11Fg020` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_nonempty_successiveCoordinateHaar` and `OAI.Generator.Tracial.represented_relative_generation` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean (declaration OAI.Generator.Tracial.nonempty_coordinateHaarData)

import Mathlib
import Definitions.Def_OAIQ11Fg020

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
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem nonempty_coordinateHaarData (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    Nonempty (CoordinateHaarData τ ω hNM D) := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
