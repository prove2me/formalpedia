-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_linked_chains_from_neighbor_boxes
-- name    : OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:48:40.025495+00:00
-- url     : https://prove2.me/theorems/047d0da9-6f28-467e-9ef5-2f660e5ea2c4
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarLinkedSource.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarLinkedSource.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric Filter`, `open scoped Manifold Pointwise Topology`):
--
--   ```lean
--   theorem PolarTiledSamplerData.linked_chains_from_neighbor_boxes
--       (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
--       (Rbox : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
--       (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β Rbox scale φ)
--       {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
--       (ψ : ∀ n, Y n →
--         (closedBall (0 : Fin (finrank ℝ
--           (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
--         (M.coneIdealBox C ExpI
--           ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0))
--           β (scale n) 1))
--       (hψ : ∀ n, Measurable (ψ n))
--       (hbij : Function.Bijective F.ExpN)
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       {Eall : Set W} (hEall : IsCompact Eall) (hne : Eall.Nonempty)
--       (γ : M.Bases)
--       (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
--         (M.boxCost T hunimod eW Eall) γ.val)
--       (w : W) (hBE : (fun x => x + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
--       (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport Eall i)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
--       (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
--       (hR : HasSubexponentialUpperBoundSeq scale R)
--       (base step : ℕ → F.N.carrier)
--       (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
--       (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n)) :
--       let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
--         M.bound_zero (cartanIdealWeightDilation T H
--           (scale n • cartanHeightSection T H (eW.symm w)))
--       let Ep := fun k => (fun x => x + w) '' normalizedPolarTemplates K ε k
--       let probe := fun k n y => S n (D.chain.probe n k (ψ n y))
--       ∃ (P : ∀ k, M.BoxProbeChains T F hunimod eW bN (Ep k) γ
--           (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i) scale (probe k))
--         (origin finish : ℕ → cartanRootIdeal H) (η : ℕ → ℝ),
--         (∀ n, F.ExpN (F.N.equiv (origin n)) = base n) ∧
--         (∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n) ∧
--         (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
--         Nonempty (M.LinkedProbeChains T F hunimod eW bN Ep γ
--           (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i)
--           scale probe P (fun n _ => origin n) (fun n _ => finish n) η)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanHeightSection`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.integrateNilpotentLieEquiv` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains` and `OAI.PolycyclicRecognition.CartanWordModel.LinkedProbeChains` (definitions bundle `OAIQ093D013` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.cartanIdealWeightDilation`, `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBox` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.nonempty_linkedSource_of_exp` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarLinkedSource.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Manifold Pointwise Topology

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

local notation "C" => heightConePreimage T eW K

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
set_option maxHeartbeats 1000000 in
theorem PolarTiledSamplerData.linked_chains_from_neighbor_boxes
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
    (Rbox : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β Rbox scale φ)
    {Y : ℕ → Type} [∀ n, MeasurableSpace (Y n)]
    (ψ : ∀ n, Y n →
      (closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0))
        β (scale n) 1))
    (hψ : ∀ n, Measurable (ψ n))
    (hbij : Function.Bijective F.ExpN)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    {Eall : Set W} (hEall : IsCompact Eall) (hne : Eall.Nonempty)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (w : W) (hBE : (fun x => x + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport Eall i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n)) :
    let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (cartanIdealWeightDilation T H
        (scale n • cartanHeightSection T H (eW.symm w)))
    let Ep := fun k => (fun x => x + w) '' normalizedPolarTemplates K ε k
    let probe := fun k n y => S n (D.chain.probe n k (ψ n y))
    ∃ (P : ∀ k, M.BoxProbeChains T F hunimod eW bN (Ep k) γ
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i) scale (probe k))
      (origin finish : ℕ → cartanRootIdeal H) (η : ℕ → ℝ),
      (∀ n, F.ExpN (F.N.equiv (origin n)) = base n) ∧
      (∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n) ∧
      (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      Nonempty (M.LinkedProbeChains T F hunimod eW bN Ep γ
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i)
        scale probe P (fun n _ => origin n) (fun n _ => finish n) η) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
