-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_boundary_comparisons
-- name    : OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:32:59.545505+00:00
-- url     : https://prove2.me/theorems/a5fc28ac-7b28-498f-8db4-5189e07843b9
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryBoundedHeight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryBoundedHeight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set`, `open scoped Manifold BigOperators`):
--
--   ```lean
--   theorem uniform_affine_bound_of_boundary_comparisons
--       (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
--       (hsub : ∀ p ε, 0 < ε → ∃ B : ℝ, ∀ g,
--         ‖(height (f p g)).toAdd - (height (f p 1)).toAdd - A.val (height g).toAdd‖ ≤
--           ε * dist 1 g + B) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ p g,
--         ‖(height (f p g)).toAdd - ((height (f p 1)).toAdd + A.val (height g).toAdd)‖ ≤ K
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.BoundaryVolumeComparison`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.positiveWeightRay` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.GeodesicMetricExistenceInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel` (definitions bundle `OAIQ093D022` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_published_inputs_and_sublinear` and `OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryBoundedHeight.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {P : Type} [SimplyConnectedSpace G] [IsIsometricSMul G G]
  (height : G →* Multiplicative W) (f : P → G → G)
  (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (RS : ∀ i, M.RayBoundaryModel F ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : ∀ i, M.RayBoundaryModel F (((M.supportIn T hunimod eW).weight i).comp (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (C : ∀ i, BoundaryVolumeComparison (RS i).action (RT i).action
    ((((M.supportIn T hunimod eW).weight i).toContinuousLinearMap).comp A.val.toContinuousLinearEquiv.toContinuousLinearMap)
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap height f)
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (metricInput : GeodesicMetricExistenceInput)
  (dynkinS : ∀ i, NilpotentDynkinExpansionInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)
  (haarS : ∀ i, NilpotentExponentialHaarInput (RS i).cone.Q.modelSpace (RS i).cone.Q.carrier)

set_option maxHeartbeats 1000000 in
include C hExpG realize hbijN chartD hchartD dynkinN metricInput dynkinS haarS in
theorem uniform_affine_bound_of_boundary_comparisons
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hsub : ∀ p ε, 0 < ε → ∃ B : ℝ, ∀ g,
      ‖(height (f p g)).toAdd - (height (f p 1)).toAdd - A.val (height g).toAdd‖ ≤
        ε * dist 1 g + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p g,
      ‖(height (f p g)).toAdd - ((height (f p 1)).toAdd + A.val (height g).toAdd)‖ ≤ K := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
