-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_nonempty_rayBoundaryComparison_of_shadows
-- name    : OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-02T19:27:48.461349+00:00
-- url     : https://prove2.me/theorems/afe2a5f2-3a29-47c6-82cc-20ad8a780d55
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanRayBoundaryComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanRayBoundaryComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace`, `open scoped Manifold ENNReal`):
--
--   ```lean
--   theorem nonempty_rayBoundaryComparison_of_shadows
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
--       (haarT : NilpotentExponentialHaarInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
--       (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
--       (jS jT : Fin M.letterCount)
--       (hjS : (M.weight jS : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αS.toLinearMap.comp
--         (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
--       (hjT : (M.weight jT : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αT.toLinearMap.comp
--         (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
--       (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (g : P → G → G)
--       {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
--       (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
--       (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
--       (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
--       (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
--       (hKS : IsCompact KS) (hKT : IsCompact KT)
--       (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
--       (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) :
--       Nonempty (RayBoundaryComparison RS RT height f)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.positiveWeightRay` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryComparison` and `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel` (definitions bundle `OAIQ093D022` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_published_inputs_and_sublinear` and `OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanRayBoundaryComparison.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} {T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)

variable [IsIsometricSMul G G] [ProperSpace G] [SimplyConnectedSpace G]

set_option maxHeartbeats 1000000 in
theorem nonempty_rayBoundaryComparison_of_shadows
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (haarS : NilpotentExponentialHaarInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (haarT : NilpotentExponentialHaarInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (jS jT : Fin M.letterCount)
    (hjS : (M.weight jS : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (hjT : (M.weight jT : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier) (g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) :
    Nonempty (RayBoundaryComparison RS RT height f) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
