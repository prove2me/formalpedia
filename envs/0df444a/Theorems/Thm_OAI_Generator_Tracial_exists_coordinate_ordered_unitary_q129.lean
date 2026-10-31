-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_ordered_unitary_q129
-- name    : OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:53:20.257764+00:00
-- url     : https://prove2.me/theorems/daf57cda-deb2-425c-9233-fc6b2c4c6ceb
-- title:
--   OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_coordinate_ordered_unitary` of [lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem exists_coordinate_ordered_unitary_q129
--       (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
--       (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
--       ∃ b : Bounded M,
--         (∀ j,b.val j ∈ unitary M.toStarSubalgebra ∧ (b.val j).val ∈ N) ∧
--         ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) b) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ129G001` of this split); `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.quotientTrace` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ129G004` of this split); `OAI.Generator.Tracial.Q` and `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.Tracial.ExactOrderedMoments` (definitions bundle `OAIQ129G011` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean (declaration OAI.Generator.Tracial.exists_coordinate_ordered_unitary)

import Mathlib
import Definitions.Def_OAIQ129G011

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
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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

theorem exists_coordinate_ordered_unitary_q129
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ b : Bounded M,
      (∀ j,b.val j ∈ unitary M.toStarSubalgebra ∧ (b.val j).val ∈ N) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) b) x := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
