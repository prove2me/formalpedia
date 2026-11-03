-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_boundary_family_with_compact_shadow
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:57:19.991651+00:00
-- url     : https://prove2.me/theorems/240041cb-3a58-4756-9abb-9bede0852e40
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryFamilyShadow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryFamilyShadow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Filter Set`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_boundary_family_with_compact_shadow
--       [SimplyConnectedSpace G]
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ₀ : M.Bases)
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
--         (cartanLog H F.D.equiv F.ExpD
--           (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
--       (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
--       (αW : W →L[ℝ] ℝ)
--       (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
--         (positiveWeightRay (αW.toLinearMap.comp
--           (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
--       (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
--       (hExpQ : IsGroupExponential ExpQ)
--       (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
--       (hchartQ : ∀ v, chartQ v = ExpQ v)
--       (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
--       (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
--       (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
--         ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
--           (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
--       (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
--       (hα : ∀ d n, α d (π n) = π (F.action d n))
--       (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
--       (A : W →L[ℝ] W) (f : P → G → G) {L error : ℝ} (hL : 0 ≤ L)
--       (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
--       (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
--         ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
--       (v₀ : W) (hv₀ : αW (A v₀) < 0)
--       {S : Type} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
--       (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
--         (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
--           (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
--           Set (cartanRootIdeal H))))
--       (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
--         n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
--       (hcover : Function.Surjective (fun g => actS g 1)) :
--       let ray := fun n : ℕ => ExpG ((n : ℝ) •
--         (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
--       ∃ (B : P → S → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ ∀ p x,
--         Tendsto (fun n => act (f p (x * ray n)) 1) atTop (𝓝 (B p (actS x 1))) ∧
--         ∃ z ∈ K, B p (actS x 1) = act (f p x) z
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.cartanHeightSection`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.CartanWordModel.Bases` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.positiveWeightRay` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneProjection` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoundaryFamilyShadow.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
theorem exists_boundary_family_with_compact_shadow
    [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : P → G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    {S : Type} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
    (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
      (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
        Set (cartanRootIdeal H))))
    (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
      n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
    (hcover : Function.Surjective (fun g => actS g 1)) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (B : P → S → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ ∀ p x,
      Tendsto (fun n => act (f p (x * ray n)) 1) atTop (𝓝 (B p (actS x 1))) ∧
      ∃ z ∈ K, B p (actS x 1) = act (f p x) z := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
