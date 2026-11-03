-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_profile_bridge_restrictions_of_basis
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:05:59.910166+00:00
-- url     : https://prove2.me/theorems/634c9e39-9143-4db8-97c5-4eb76c9358ca
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformProfileBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformProfileBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Metric Set Filter`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_uniform_profile_bridge_restrictions_of_basis
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ₀ : M.Bases)
--       {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
--       (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
--       (C : Set (H →ₗ[ℝ] ℝ))
--       {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
--       (β : M.ConeIdealBases C)
--       (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
--         ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
--       (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
--         cartanRootIdeal H)
--       (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
--       (γ : M.Bases)
--       (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E) γ.val)
--       (hbox : ∀ r R : ℝ, M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E γ r R =
--         exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
--           (exponentialRescaleBasis
--             (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
--               (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
--               bQ lift hlift)
--             (Sum.elim
--               (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
--               (fun _ => 0)) r) R)
--       (K : ℝ) (hK : 0 ≤ K)
--       (hbr : ∀ r : ℝ, 0 ≤ r →
--         let B := exponentialRescaleBasis
--           (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
--             (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
--             bQ lift hlift)
--           (Sum.elim
--             (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
--             (fun _ => 0)) r
--         ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ K)
--       {lo : ℝ} (hlo : 0 < lo)
--       (hcost : ∀ j, lo ≤ M.coneIdealWordCost C
--         ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
--       {Q : Type} [Group Q]
--       (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
--       (πQ : F.N.carrier →* Q)
--       (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) =
--         ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
--       (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
--       : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
--         StrictMono scale → Tendsto scale atTop atTop →
--         (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
--         ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
--         ∃ S RD : ℕ → ℝ,
--           (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
--           HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
--           ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
--           ∀ᶠ n in atTop, ∀ {endpoint : G} (path : Path (1 : G) endpoint) (bridge : G),
--             PathMetricBound path (A * scale n) (B * (1 + Real.log (2 + scale n))) →
--             (∀ t, ∃ w ∈ E, ‖(π (path t)).toAdd - scale n • w‖ ≤
--               2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
--             ‖(π endpoint).toAdd‖ ≤ δ * scale n →
--             dist 1 bridge ≤ δ * scale n →
--             ∃ (u : F.N.carrier) (d : F.D.carrier),
--               F.inclusionN u * F.inclusionD d = endpoint * bridge ∧
--               ∀ z ∈ cell,
--                 (∃ (i : M.coneWordIdeal C)
--                   (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
--                   u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
--                     F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
--                   ‖(M.coneIdealBoxBasis C
--                     ((M.supportIn T hunimod eW).weightSupport E) β (scale n)).equivFun i‖ ≤ S n) ∧
--                 ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
--                   hbijD (d * z.2))‖ ≤ RD n
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.exponentialCoordinateBox` and `OAI.PolycyclicRecognition.quotientLinearSection` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.basisWithQuotientLifts` and `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordCost` and `OAI.PolycyclicRecognition.CartanWordModel.coneMixedWords` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBoxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordList`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedVector` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformProfileBridge.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
theorem exists_uniform_profile_bridge_restrictions_of_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.ConeIdealBases C)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) γ.val)
    (hbox : ∀ r R : ℝ, M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E γ r R =
      exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis
          (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
            (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
            bQ lift hlift)
          (Sum.elim
            (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
            (fun _ => 0)) r) R)
    (K : ℝ) (hK : 0 ≤ K)
    (hbr : ∀ r : ℝ, 0 ≤ r →
      let B := exponentialRescaleBasis
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
          (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
          bQ lift hlift)
        (Sum.elim
          (fun j => M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
          (fun _ => 0)) r
      ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ K)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ j, lo ≤ M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E) (β.val j))
    {Q : Type} [Group Q]
    (ExpQ : ((cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule) → Q)
    (πQ : F.N.carrier →* Q)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) =
      ExpQ ((M.coneWordIdeal C).toSubmodule.mkQ v))
    (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
    : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ S RD : ℕ → ℝ,
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ {endpoint : G} (path : Path (1 : G) endpoint) (bridge : G),
          PathMetricBound path (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E, ‖(π (path t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π endpoint).toAdd‖ ≤ δ * scale n →
          dist 1 bridge ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = endpoint * bridge ∧
            ∀ z ∈ cell,
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  ((M.supportIn T hunimod eW).weightSupport E) β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
