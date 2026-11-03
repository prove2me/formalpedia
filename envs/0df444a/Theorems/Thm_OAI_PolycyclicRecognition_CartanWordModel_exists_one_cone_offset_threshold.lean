-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_one_cone_offset_threshold
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T20:02:07.703349+00:00
-- url     : https://prove2.me/theorems/440480ba-ed32-450b-b7f3-fff75a0aafc8
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOneConeThreshold.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOneConeThreshold.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set`, `open scoped Manifold Topology ENNReal NNReal BigOperators`):
--
--   ```lean
--   theorem exists_one_cone_offset_threshold
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ x, chartN x = F.ExpN x)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ x, chartD x = F.ExpD x)
--       (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
--       (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
--       (π : G →* Multiplicative W)
--       (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
--       (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
--       (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
--         [ErgodicSMul G (NormalizedPair G Λ) μ],
--         ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
--       (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
--       (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ : M.Bases)
--       (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
--         (M.boxCost T hunimod eW Eall) γ.val)
--       (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
--       (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
--       (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
--       (βD : WordBasisSelections X (boundedBracketWords d))
--       (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
--         (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
--       {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
--       (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       {cD : ℕ} (aD : DynkinCoefficients cD 2)
--       (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
--       (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (pivot : Fin M.letterCount → H) (i : Fin M.letterCount)
--       (hcanonical : cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
--       (hunit : ‖eW (heightProjection T.character (pivot i))‖ = 1)
--       (hcontact : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
--         (eW (heightProjection T.character (pivot i))) =
--           ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
--       (hpositive : 0 < M.weight i (pivot i))
--       {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
--       (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
--         M.boxCost T hunimod eW Eall w ≤ hi)
--       (hgap : (M.bound : ℝ) * hi < c * lo)
--       (σchamber : Fin M.letterCount → Bool)
--       (hσchamber : (weightChamber (fun j =>
--         ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
--       (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
--       [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
--       (K : ProperCone ℝ (StrongDual ℝ W))
--       (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
--       (hiK : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
--       (A : templateSymmetryGroup (M.supportIn T hunimod eW))
--       (Ds : M.MeasuredCone F (heightConePreimage T eW K))
--       (dynkinI : NilpotentDynkinExpansionInput Ds.I.modelSpace Ds.I.carrier)
--       (haarI : NilpotentExponentialHaarInput Ds.I.modelSpace Ds.I.carrier)
--       (Dt₀ : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
--       (haarQt : NilpotentExponentialHaarInput Dt₀.Q.modelSpace Dt₀.Q.carrier)
--       (haarIt : NilpotentExponentialHaarInput Dt₀.I.modelSpace Dt₀.I.carrier) :
--       ∃ coeff : Fin M.letterCount → ℕ,
--         (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
--           transformedPolarCone K A.val → coeff j = 0) ∧
--         (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
--           transformedPolarCone K A.val → 0 < coeff j) ∧
--         ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
--         ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
--           haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
--         row.mode = i → row.label₁ = A → row.label₂ = A →
--           (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
--             (row.offset₂ - row.offset₁) ≤ 0
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanHeightSection`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.normalizedPairAction` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ErgodicDecompositionInput`, `OAI.PolycyclicRecognition.ReducedCohomologyInput` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ZeroMeanL2` and `OAI.PolycyclicRecognition.stationaryL2Mean` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.transformedPolarCone` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.finiteDynkinPolynomial` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.normalizedPairContinuousAction`, `OAI.PolycyclicRecognition.weightChamber` and `OAI.PolycyclicRecognition.zeroMeanL2Action` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.CartanWordModel.samplingPolytope` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.normalizedPair_polishSpace`, `OAI.PolycyclicRecognition.zeroMeanL2Isometric` and `OAI.PolycyclicRecognition.zeroMeanL2SMulComm` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOneConeThreshold.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

set_option maxHeartbeats 1000000 in
theorem exists_one_cone_offset_threshold
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H) (i : Fin M.letterCount)
    (hcanonical : cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (hiK : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (Ds : M.MeasuredCone F (heightConePreimage T eW K))
    (dynkinI : NilpotentDynkinExpansionInput Ds.I.modelSpace Ds.I.carrier)
    (haarI : NilpotentExponentialHaarInput Ds.I.modelSpace Ds.I.carrier)
    (Dt₀ : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
    (haarQt : NilpotentExponentialHaarInput Dt₀.Q.modelSpace Dt₀.Q.carrier)
    (haarIt : NilpotentExponentialHaarInput Dt₀.I.modelSpace Dt₀.I.carrier) :
    ∃ coeff : Fin M.letterCount → ℕ,
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
        transformedPolarCone K A.val → coeff j = 0) ∧
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
        transformedPolarCone K A.val → 0 < coeff j) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.mode = i → row.label₁ = A → row.label₂ = A →
        (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (row.offset₂ - row.offset₁) ≤ 0 := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
