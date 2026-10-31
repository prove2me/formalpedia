-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_reduced_unitary
-- name    : OAI.Generator.Tracial.exists_coordinate_reduced_unitary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T10:00:13.4281+00:00
-- url     : https://prove2.me/theorems/ce27425e-c05d-4943-930f-4fcf40055133
-- title:
--   OAI.Generator.Tracial.exists_coordinate_reduced_unitary: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_coordinate_reduced_unitary` of [lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem exists_coordinate_reduced_unitary
--       (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
--       (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
--       ∃ a : Bounded M,
--         (∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) ∧
--         ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.quotientTrace`, `OAI.UltrapowerBridge.traceCongruence` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.ReducedOrderedMoments` (definitions bundle `OAIQ11Fg014` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_coordinate_haar_endpoints` and `OAI.Generator.Tracial.nonempty_coordinateHaarData` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinateUnitaries.lean (declaration OAI.Generator.Tracial.exists_coordinate_reduced_unitary)

import Mathlib
import Definitions.Def_OAIQ11Fg014

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
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

theorem exists_coordinate_reduced_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ a : Bounded M,
      (∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) ∧
      ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
