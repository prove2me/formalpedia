-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_strict_admissible_unit_patch
-- name    : OAI.Generator.Tracial.exists_strict_admissible_unit_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:51:54.552368+00:00
-- url     : https://prove2.me/theorems/64e0385a-325b-445b-b363-2b3636620aa9
-- title:
--   OAI.Generator.Tracial.exists_strict_admissible_unit_patch: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_strict_admissible_unit_patch` of [lean/OAI/Analysis/FactorGeneration/LocalPatches.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalPatches.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_strict_admissible_unit_patch
--       (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
--       (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
--       (v : PartialUnitary M)
--       (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
--       (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
--       ∃ u : PartialUnitary M,
--         PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) u ∧
--         v ≤ u ∧ (τ.trace v.support.val).re < (τ.trace u.support.val).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.identityProjection` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.Tracial.patchingTolerance` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.Tracial.PartialUnitary` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.PatchingAdmissibleIn` (definitions bundle `OAIQ11Fg009` of this split); `OAI.Generator.Tracial.PartialUnitary.instPartialOrder` (definitions bundle `OAIQ11Fg012` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_finite_partial_independence` and `OAI.Generator.Tracial.exists_supported_corner_partial_sequence` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalPatches.lean (declaration OAI.Generator.Tracial.exists_strict_admissible_unit_patch)

import Mathlib
import Definitions.Def_OAIQ11Fg012

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_strict_admissible_unit_patch
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (v : PartialUnitary M)
    (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
    ∃ u : PartialUnitary M,
      PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) u ∧
      v ≤ u ∧ (τ.trace v.support.val).re < (τ.trace u.support.val).re := by
  sorry

end Generator.Tracial

end

end OAI
end
