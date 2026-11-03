-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_increments_tendsto_template_labels_of_invariant_probability
-- name    : OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:08:20.257618+00:00
-- url     : https://prove2.me/theorems/db1380f4-d2af-4132-88ae-f643ee6d4cb0
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanStationaryTemplateIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanStationaryTemplateIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Metric Set`, `open scoped Manifold NNReal ENNReal Pointwise`):
--
--   ```lean
--   theorem increments_tendsto_template_labels_of_invariant_probability
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
--       (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
--       [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
--       (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
--       (hvan : ∀ (ν : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure ν]
--         [ErgodicSMul G (NormalizedPair G Λ) ν],
--         ReducedCohomologyInput G (ZeroMeanL2 (W := W) ν))
--       (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
--       (hLip : LipschitzWith K (fun g => (π g).toAdd))
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
--         (cartanLog H F.D.equiv F.ExpD
--           (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       (v : H) :
--       Filter.Tendsto (fun r : ℝ => ∫⁻ p,
--         ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
--           (Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
--             A.val (eW (heightProjection T.character v))))) ∂μ)
--         Filter.atTop (nhds 0)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.normalizedPairAction` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ErgodicDecompositionInput` and `OAI.PolycyclicRecognition.ReducedCohomologyInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ZeroMeanL2`, `OAI.PolycyclicRecognition.cartanLog` and `OAI.PolycyclicRecognition.stationaryL2Mean` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.normalizedPairContinuousAction`, `OAI.PolycyclicRecognition.pairHeight` and `OAI.PolycyclicRecognition.zeroMeanL2Action` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.normalizedPair_polishSpace`, `OAI.PolycyclicRecognition.zeroMeanL2Isometric` and `OAI.PolycyclicRecognition.zeroMeanL2SMulComm` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_increment_mem_template_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanStationaryTemplateIncrement.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
theorem increments_tendsto_template_labels_of_invariant_probability
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (ν : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure ν]
      [ErgodicSMul G (NormalizedPair G Λ) ν],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) ν))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : H) :
    Filter.Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
        (Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v))))) ∂μ)
      Filter.atTop (nhds 0) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
