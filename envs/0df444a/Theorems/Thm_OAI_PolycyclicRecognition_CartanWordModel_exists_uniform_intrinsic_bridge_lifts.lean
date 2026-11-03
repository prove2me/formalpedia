-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_intrinsic_bridge_lifts
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:58.095208+00:00
-- url     : https://prove2.me/theorems/e681d81e-2d60-4f40-bfa3-d82f6962b18a
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformIntrinsicBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformIntrinsicBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Metric Set Filter`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_uniform_intrinsic_bridge_lifts
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         hbijN dynkinN
--         (cartanLog H F.D.equiv F.ExpD
--           hbijD d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
--       (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
--       (C : Set (H →ₗ[ℝ] ℝ))
--       {I J : Type} [Fintype I] [Fintype J]
--       (bI : Basis I ℝ (M.coneWordIdeal C))
--       (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
--       (lift : J → cartanRootIdeal H)
--       (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
--       {Q : Type} [Group Q]
--       (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
--       (πQ : F.N.carrier →* Q)
--       (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
--       (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
--       (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
--       (K : ℝ) (hK : 0 ≤ K)
--       (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
--         |(exponentialRescaleBasis
--           (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
--           (Sum.elim cost (fun _ => 0)) r).repr
--             ⁅exponentialRescaleBasis
--               (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
--               (Sum.elim cost (fun _ => 0)) r i,
--              exponentialRescaleBasis
--               (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
--               (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
--       : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH : ℕ → ℝ),
--         StrictMono scale → Tendsto scale atTop atTop →
--         (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
--         HasSubexponentialUpperBoundSeq scale RN → HasSubexponentialUpperBoundSeq scale RH →
--         ∃ S RD : ℕ → ℝ,
--           (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
--           HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
--           ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
--         ∀ᶠ n in atTop, ∀ (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G),
--           u₂ ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
--             (exponentialRescaleBasis
--               (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
--               (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
--           ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
--             hbijD d₂)‖ ≤ RH n →
--           ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n →
--           dist 1 g ≤ δ * scale n →
--           ∃ (u : F.N.carrier) (d : F.D.carrier),
--             F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
--             ∀ z ∈ cell,
--               (∃ (i : M.coneWordIdeal C)
--                 (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
--                 u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
--                   F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
--                 ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n) ∧
--               ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
--                 hbijD
--                 (d * z.2))‖ ≤ RD n
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.CartanWordModel.Bases` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.exponentialCoordinateBox` and `OAI.PolycyclicRecognition.quotientLinearSection` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.basisWithQuotientLifts` and `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformIntrinsicBridge.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_intrinsic_bridge_lifts
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN
      (cartanLog H F.D.equiv F.ExpD
        hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {I J : Type} [Fintype I] [Fintype J]
    (bI : Basis I ℝ (M.coneWordIdeal C))
    (bQ : Basis J ℝ ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : J → cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    {Q : Type} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    (cost : I → ℝ) {lo : ℝ} (hlo : 0 < lo) (hcost : ∀ i, lo ≤ cost i)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k,
      |(exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r).repr
          ⁅exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r i,
           exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) r j⁆ k| ≤ K)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale RN RH : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ RN n) → (∀ n, 0 ≤ RH n) →
      HasSubexponentialUpperBoundSeq scale RN → HasSubexponentialUpperBoundSeq scale RH →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ n in atTop, ∀ (u₂ : F.N.carrier) (d₂ : F.D.carrier) (g : G),
        u₂ ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (exponentialRescaleBasis
            (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule bI bQ lift hlift)
            (Sum.elim cost (fun _ => 0)) (scale n)) (RN n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          hbijD d₂)‖ ≤ RH n →
        ‖(π (F.inclusionD d₂)).toAdd‖ ≤ δ * scale n →
        dist 1 g ≤ δ * scale n →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = (F.inclusionN u₂ * F.inclusionD d₂) * g ∧
          ∀ z ∈ cell,
            (∃ (i : M.coneWordIdeal C)
              (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
              u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
              ‖(exponentialRescaleBasis bI cost (scale n)).equivFun i‖ ≤ S n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              hbijD
              (d * z.2))‖ ≤ RD n := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
