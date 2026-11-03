-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_concentrated_profile_frames
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:22:48.79738+00:00
-- url     : https://prove2.me/theorems/71d4de4e-7e2f-4c38-bf41-9a665f3a0b2c
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanConcentratedFrames.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanConcentratedFrames.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace`, `open scoped Manifold Topology NNReal ENNReal`):
--
--   ```lean
--   theorem exists_concentrated_profile_frames
--       {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
--       [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
--       [∀ n, Nonempty (K n)]
--       [Nonempty (Fin M.letterCount)]
--       [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
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
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E) β.val)
--       (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
--       {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
--       (hcost : ∀ w : M.wordList,
--         lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
--       (hgap : (M.bound : ℝ) * hi < c * lo)
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
--       (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
--       (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
--       (Eprobe : Fin 3 → Set W)
--       (probe : Fin 3 → ∀ n, K n → F.N.carrier)
--       (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
--         (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
--       (origin base : ℕ → cartanRootIdeal H)
--       (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
--         (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
--         scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
--       (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
--       (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
--       (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
--       (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
--       (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
--       (hEV : ∀ k, Eprobe k ⊆ V)
--       (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
--       (σ : Fin M.letterCount → Bool)
--       (hσ : (weightChamber (fun i =>
--         ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
--       let b := WordBasisSelections.basis X (boundedBracketWords d) βD
--       let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
--       let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
--       let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
--         ((heightProjection T.character).comp H.incl.toLinearMap)
--       ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
--         IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
--         ∃ z₀ : ℕ → Z,
--         (∀ᶠ n in atTop,
--           F.profileChart (br n) (z₀ n).val =
--             Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
--           h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
--         ∀ [CompactSpace Z]
--       (ν : ∀ n, ProbabilityMeasure (K n))
--       [∀ n, (ν n : Measure (K n)).InnerRegular]
--       [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
--       [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
--       (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
--       (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : C(Z, W) × C(Z, W))
--       (_hf : f ∈ (limitLaw : Measure _).support)
--       (_haffine : ∀ s z, (if s then f.2 else f.1) z =
--         A (eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
--       (_hlim :
--         let J := fun n g => (π ((p n).val.1 g)).toAdd
--         let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
--         let r := fun n => max (Real.log (scale n)) 0
--         let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
--         let bD := fun n => exponentialRescaleBasis
--           (WordBasisSelections.basis X (boundedBracketWords d) βD)
--           (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
--         Tendsto (fun n => ProbabilityMeasure.map
--           (cellProbabilityMeasure volume
--             (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
--             (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
--           (f := (fun y =>
--             ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
--               (origin n)).restrict Z,
--              (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
--               (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)),
--       let chart := fun n (z : Z) => F.profileChart (br n) z.val
--       let q := fun z : Z => h (b.equivFun.symm z.val)
--       ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
--         (good : ∀ n, Set (K n)),
--         (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
--         (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
--           (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
--         ∀ᶠ n in atTop,
--           (∀ s : Bool,
--             ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
--               (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
--                 (if s then base n else origin n)) (Real.log (scale n))
--               (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
--           (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
--             ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
--               (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
--                 (D.vertex k n y j)) (Real.log (scale n))
--               (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
--           ∀ y ∈ good n, ∀ k : Fin 3,
--             ∃ path : Path (1 : G) (basedImage (p n).val.1
--                 (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
--                   (sample n) (D.vertex k n y 0) * chart n (z₀ n))
--                 (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
--                   (sample n) (D.vertex k n y (Fin.last (P k).length)) * chart n (z₀ n))),
--               PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
--               ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
--                 ‖(π (path t)).toAdd - scale n • w‖ ≤
--                   4 * scale n * η n + C * (1 + Real.log (2 + scale n))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanFactorModel.measurable_fixed_sampledProbeProfile`, `OAI.PolycyclicRecognition.CartanFactorModel.profileChart`, `OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile`, `OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeSuffix`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.LipschitzPairBounds`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.cellProbabilityMeasure`, `OAI.PolycyclicRecognition.coordinate_cube_mass` and `OAI.PolycyclicRecognition.normalizedPairAction` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ErgodicDecompositionInput`, `OAI.PolycyclicRecognition.PathMetricBound`, `OAI.PolycyclicRecognition.ReducedCohomologyInput` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ZeroMeanL2`, `OAI.PolycyclicRecognition.basedImage` and `OAI.PolycyclicRecognition.stationaryL2Mean` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.normalizedPairContinuousAction`, `OAI.PolycyclicRecognition.weightChamber` and `OAI.PolycyclicRecognition.zeroMeanL2Action` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains` and `OAI.PolycyclicRecognition.CartanWordModel.LinkedProbeChains` (definitions bundle `OAIQ093D013` of this split); `OAI.PolycyclicRecognition.normalizedPair_polishSpace`, `OAI.PolycyclicRecognition.zeroMeanL2Isometric` and `OAI.PolycyclicRecognition.zeroMeanL2SMulComm` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanConcentratedFrames.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D013
import Definitions.Def_OAIQ093D015

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

set_option maxHeartbeats 1000000 in
theorem exists_concentrated_profile_frames
    {K : ℕ → Type} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
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
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∃ z₀ : ℕ → Z,
      (∀ᶠ n in atTop,
        F.profileChart (br n) (z₀ n).val =
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : C(Z, W) × C(Z, W))
    (_hf : f ∈ (limitLaw : Measure _).support)
    (_haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (_hlim :
      let J := fun n g => (π ((p n).val.1 g)).toAdd
      let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
      let r := fun n => max (Real.log (scale n)) 0
      let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
      let bD := fun n => exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
      Tendsto (fun n => ProbabilityMeasure.map
        (cellProbabilityMeasure volume
          (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
        (f := (fun y =>
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (origin n)).restrict Z,
           (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (base n)).restrict Z))) (((F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (origin n) Z).prodMk (F.measurable_fixed_sampledProbeProfile hN hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (base n) Z)).aemeasurable)) atTop (𝓝 limitLaw)),
    let chart := fun n (z : Z) => F.profileChart (br n) z.val
    let q := fun z : Z => h (b.equivFun.symm z.val)
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        (∀ s : Bool,
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
              (if s then base n else origin n)) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) (sample n)
              (D.vertex k n y j)) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
                (sample n) (D.vertex k n y 0) * chart n (z₀ n))
              (x n * F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n))
                (sample n) (D.vertex k n y (Fin.last (P k).length)) * chart n (z₀ n))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
