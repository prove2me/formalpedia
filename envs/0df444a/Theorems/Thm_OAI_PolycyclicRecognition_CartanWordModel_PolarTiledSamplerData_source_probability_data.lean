-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_source_probability_data
-- name    : OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:56:27.5172+00:00
-- url     : https://prove2.me/theorems/421eb59d-38ab-45a4-b8ac-c2f7caf6d1f5
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarSourceProbability.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarSourceProbability.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace`, `open scoped Manifold Pointwise`):
--
--   ```lean
--   theorem PolarTiledSamplerData.source_probability_data
--       (D : M.MeasuredCone F C)
--       (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
--       {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
--       (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
--       (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
--       (P : M.PolarTiledSamplerData T F hunimod eW K
--         (D.maps.expI ∘ D.I.equiv) D.maps.inclusion bN ε β R scale φ) :
--       let Z := TiledProbeChainData.sourceQuotientCell
--         (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
--         (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
--         (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
--         (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
--         (scale := scale) (φ := φ) (ι := D.maps.inclusion)
--         (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
--         (Q := D.Q) (chartQ := D.maps.chartQ)
--       let J := fun n => TiledProbeChainData.sourceKernelCell
--         (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
--         (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
--         (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
--         (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
--         (hrange := D.maps.inclusion_range) n
--       let μQ := D.measures.measureQ
--       let μK := D.kernelMeasure M F C
--       ∃ (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
--         (_hZ0 : μQ Z ≠ 0) (_hZt : μQ Z ≠ ⊤)
--         (_hJ0 : ∀ n, μK (J n) ≠ 0) (_hJt : ∀ n, μK (J n) ≠ ⊤)
--         (h0 : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ 0)
--         (ht : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ ⊤),
--         IsCompact Z ∧ (∀ n, IsCompact (J n)) ∧
--         (∀ n, Nonempty (Z ×ˢ J n)) ∧
--         (∀ n, (cellSubtypeProbability (μQ.prod μK) (Z ×ˢ J n)
--           (hZm.prod (hJm n)) (h0 n) (ht n) : Measure (Z ×ˢ J n)).InnerRegular) ∧
--         ∃ v : ℝ, 0 < v ∧ ∀ n,
--           (μK (J n)).toReal = v * Real.exp (scale n *
--             (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.SupportDatum.templateSupport` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.cellSubtypeProbability` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMaps` (definitions bundle `OAIQ093D019` of this split); `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceQuotientCell` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone`, `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMeasures`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.kernelMeasure` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceKernelCell` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarSourceProbability.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace
open scoped Manifold Pointwise

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

set_option maxHeartbeats 1000000 in
theorem PolarTiledSamplerData.source_probability_data
    (D : M.MeasuredCone F C)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (R : ℝ) (scale : ℕ → ℝ) (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
    (P : M.PolarTiledSamplerData T F hunimod eW K
      (D.maps.expI ∘ D.I.equiv) D.maps.inclusion bN ε β R scale φ) :
    let Z := TiledProbeChainData.sourceQuotientCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
      (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
      (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
      (scale := scale) (φ := φ) (ι := D.maps.inclusion)
      (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
      (Q := D.Q) (chartQ := D.maps.chartQ)
    let J := fun n => TiledProbeChainData.sourceKernelCell
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
      (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
      (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
      (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
      (hrange := D.maps.inclusion_range) n
    let μQ := D.measures.measureQ
    let μK := D.kernelMeasure M F C
    ∃ (hZm : MeasurableSet Z) (hJm : ∀ n, MeasurableSet (J n))
      (_hZ0 : μQ Z ≠ 0) (_hZt : μQ Z ≠ ⊤)
      (_hJ0 : ∀ n, μK (J n) ≠ 0) (_hJt : ∀ n, μK (J n) ≠ ⊤)
      (h0 : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ 0)
      (ht : ∀ n, (μQ.prod μK) (Z ×ˢ J n) ≠ ⊤),
      IsCompact Z ∧ (∀ n, IsCompact (J n)) ∧
      (∀ n, Nonempty (Z ×ˢ J n)) ∧
      (∀ n, (cellSubtypeProbability (μQ.prod μK) (Z ×ˢ J n)
        (hZm.prod (hJm n)) (h0 n) (ht n) : Measure (Z ×ˢ J n)).InnerRegular) ∧
      ∃ v : ℝ, 0 < v ∧ ∀ n,
        (μK (J n)).toReal = v * Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (normalizedPolarTemplates K ε 0)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
