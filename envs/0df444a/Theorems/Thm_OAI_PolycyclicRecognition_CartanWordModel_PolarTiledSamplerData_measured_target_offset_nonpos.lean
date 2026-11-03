-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_measured_target_offset_nonpos
-- name    : OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T20:03:16.655408+00:00
-- url     : https://prove2.me/theorems/0ab91622-fe0c-4fba-9a48-dc549c08c1c4
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarMeasuredOffset.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarMeasuredOffset.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace`, `open scoped Manifold Pointwise Topology BigOperators NNReal`):
--
--   ```lean
--   theorem PolarTiledSamplerData.measured_target_offset_nonpos
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
--       (hE : IsCompact Eall) (hne : Eall.Nonempty) (γaux : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
--         (M.boxCost T hunimod eW Eall) γ.val)
--       (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport Eall i)
--       {c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
--       (hcost : ∀ w : M.wordList,
--         lo ≤ M.boxCost T hunimod eW Eall w ∧ M.boxCost T hunimod eW Eall w ≤ hi)
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
--       (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
--       (hscale1 : ∀ n, 1 ≤ scale n)
--       (hBE : (fun z => z + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
--       (radius : ℕ → ℝ) (hradius0 : ∀ n, 0 ≤ radius n)
--       (hradius : HasSubexponentialUpperBoundSeq scale radius)
--       (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
--       (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
--       (hφsource : ∀ n z, D.maps.inclusion (φ n z) =
--         (S n).symm (step n) * D.maps.inclusion z * ((S n).symm (step n))⁻¹)
--       (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
--       (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
--       (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
--       (hEc : ∀ k, IsCompact (Ep k)) (hEconv : ∀ k, Convex ℝ (Ep k))
--       (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Ep k)
--       (hEV : ∀ k, Ep k ⊆ V)
--       (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' Eall)
--       (σchamber : Fin M.letterCount → Bool)
--       (hσchamber : (weightChamber (fun i =>
--         ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σchamber).Nonempty)
--       (hchartN : ∀ v, chartN v = F.ExpN v)
--       (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
--       [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
--       (profile : ℕ → F.N.carrier → Profiles) (hp : ∀ n, Measurable (profile n))
--       (hactual : ∀ n q, q ∈ (fun v => v * base n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 ∪
--         (fun v => v * base n * step n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 → ∀ z,
--         (profile n q).val z = rescaledMapProfile
--           (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
--           (max (Real.log (scale n)) 0)
--           (F.profileChart (exponentialRescaleBasis
--             (WordBasisSelections.basis X (boundedBracketWords d) βD)
--             (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
--             (max (Real.log (scale n)) 0))) z)
--       (law : ProbabilityMeasure (Profiles × Profiles))
--       (hlaw : Tendsto (fun n => ProbabilityMeasure.map
--         (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
--           Eall γ (scale n) (base n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
--         atTop (𝓝 law))
--       (bval : Bool → W) (f : Profiles × Profiles)
--       (hf : f ∈ (law : Measure (Profiles × Profiles)).support)
--       (haffine : ∀ s z,
--         eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
--         (if s then f.2 else f.1).val z = A.val (eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
--       (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
--       (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
--       (hε : 0 < ε) (hRbox : 0 ≤ Rbox)
--       (hβsource : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
--       (bItarget : Basis (Fin (finrank ℝ
--         (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
--         ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
--       (hβtarget : M.IsMaximizingConeIdealBasis
--         (heightConePreimage T eW (transformedPolarCone K A.val)) bItarget
--         ((M.supportIn T hunimod eW).weightSupport (A.val '' normalizedPolarTemplates K ε 2))
--         βtarget)
--       (hS : ∀ n v, S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv
--         (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)) v)))
--       (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
--       (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
--       (hbridge : ∀ᶠ n in atTop, ∀ y : Y n,
--         dist (F.inclusionN (coneProbeSecond (S n).toMulEquiv (base n)
--             (y.val.2 : F.N.carrier) ((S n).symm (step n))) *
--             Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
--           (F.inclusionN (base n * S n ((y.val.2 : F.N.carrier) * σ y.val.1)) *
--             Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
--       (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
--       (actionQ : F.D.carrier →* MulAut Dt.Q.carrier) (act : G →* Equiv.Perm Dt.Q.carrier)
--       (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q =
--         Dt.maps.quotient u * actionQ d q)
--       (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
--       (hcell0 : ((μN).prod νD) cell ≠ 0) (hcelltop : ((μN).prod νD) cell ≠ ⊤)
--       (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
--       (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
--         ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions Dt.maps.quotient μQ μI νD scale P₂,
--           μN = Measure.map (quotientSectionHomeomorph Dt.maps.quotient Dt.maps.quotient_continuous
--             R.sectionMap R.section_rightInverse).symm ((μQ).prod μI) ∧
--           ∀ᶠ n in atTop, R.ControlsTwoPaths
--             (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
--             π cell
--             ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 0)
--             ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 2)
--             (fun n => 2 * η n) Cp Cp δtarget n)
--       (ell : W →L[ℝ] ℝ)
--       (hHaar : ∀ (g : G) (E : Set Dt.Q.carrier), μQ (act g '' E) =
--         ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μQ E) :
--       ell (bval true - bval false) ≤ 0
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanHeightSection`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanFactorModel.profileChart`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.coneProbeSecond`, `OAI.PolycyclicRecognition.normalizedPairAction`, `OAI.PolycyclicRecognition.normalizedPolarTemplates` and `OAI.PolycyclicRecognition.quotientSectionHomeomorph` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ErgodicDecompositionInput`, `OAI.PolycyclicRecognition.ReducedCohomologyInput` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ZeroMeanL2` and `OAI.PolycyclicRecognition.stationaryL2Mean` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.transformedPolarCone` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.CartanWordModel.translatedGroupBoxProbability` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.finiteDynkinPolynomial`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordCost`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedWords` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.MeasuredProbeRegions` and `OAI.PolycyclicRecognition.MeasuredProbeRegions.ControlsTwoPaths` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.normalizedPairContinuousAction`, `OAI.PolycyclicRecognition.weightChamber` and `OAI.PolycyclicRecognition.zeroMeanL2Action` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.normalizedPair_polishSpace`, `OAI.PolycyclicRecognition.zeroMeanL2Isometric` and `OAI.PolycyclicRecognition.zeroMeanL2SMulComm` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.cartanIdealWeightDilation`, `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.IsMaximizingConeIdealBasis`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordList`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedVector` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMaps` (definitions bundle `OAIQ093D019` of this split); `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceQuotientCell` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceSection` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone`, `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMeasures`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.kernelMeasure`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.sectionMeasure` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceKernelCell` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarMeasuredOffset.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace
open scoped Manifold Pointwise Topology BigOperators NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

variable (D : M.MeasuredCone F (heightConePreimage T eW K))
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  {ε : ℝ} (β : M.ConeIdealBases (heightConePreimage T eW K)) (Rbox : ℝ) (scale : ℕ → ℝ)
  (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
  (P : M.PolarTiledSamplerData (EG := EG) (G := G) (W := W) (I := D.I.carrier) T F hunimod eW K
    (fun v : M.coneWordIdeal (heightConePreimage T eW K) => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN ε β Rbox scale φ)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)

local notation "ZQ" => TiledProbeChainData.sourceQuotientCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ)
local notation "J" => fun n => TiledProbeChainData.sourceKernelCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
  (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
  (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
  (hrange := D.maps.inclusion_range) n
local notation "Y" => fun n : ℕ => {p : D.Q.carrier × D.maps.quotient.ker // p ∈ Set.prod ZQ (J n)}
local notation "σ" => TiledProbeChainData.sourceSection
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)

variable (Eall : Set W) (γ : M.Bases) (δ : ℝ) (w : W)
  (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier) (base step : ℕ → F.N.carrier)

local notation "Ep" => fun k => (fun z => z + w) '' normalizedPolarTemplates K ε k

variable {I : Type} [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [IsTopologicalGroup F.N.carrier] [MeasurableMul F.D.carrier]

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (βtarget : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
local notation "CT" => heightConePreimage T eW (transformedPolarCone K A.val)
variable (Dt : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
  [IsTopologicalGroup Dt.Q.carrier]
local notation "μN" => Dt.sectionMeasure M F CT Dt.maps.sectionMap Dt.maps.section_rightInverse
local notation "μQ" => Dt.measures.measureQ
local notation "μI" => Dt.kernelMeasure M F CT
local notation "P₂" => Finset.sum Finset.univ (fun j => M.coneIdealWordCost
  (heightConePreimage T eW (transformedPolarCone K A.val))
  (SupportDatum.weightSupport (M.supportIn T hunimod eW) (A.val '' normalizedPolarTemplates K ε 2))
  (βtarget.val j))

set_option maxHeartbeats 1000000 in
theorem PolarTiledSamplerData.measured_target_offset_nonpos
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
    (hE : IsCompact Eall) (hne : Eall.Nonempty) (γaux : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport Eall i)
    {c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW Eall w ∧ M.boxCost T hunimod eW Eall w ≤ hi)
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
    (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (hscale1 : ∀ n, 1 ≤ scale n)
    (hBE : (fun z => z + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (radius : ℕ → ℝ) (hradius0 : ∀ n, 0 ≤ radius n)
    (hradius : HasSubexponentialUpperBoundSeq scale radius)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
    (hφsource : ∀ n z, D.maps.inclusion (φ n z) =
      (S n).symm (step n) * D.maps.inclusion z * ((S n).symm (step n))⁻¹)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Ep k)) (hEconv : ∀ k, Convex ℝ (Ep k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Ep k)
    (hEV : ∀ k, Ep k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' Eall)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σchamber).Nonempty)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (profile : ℕ → F.N.carrier → Profiles) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 ∪
      (fun v => v * base n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (Profiles × Profiles))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
        Eall γ (scale n) (base n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 law))
    (bval : Bool → W) (f : Profiles × Profiles)
    (hf : f ∈ (law : Measure (Profiles × Profiles)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (hε : 0 < ε) (hRbox : 0 ≤ Rbox)
    (hβsource : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (bItarget : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (hβtarget : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bItarget
      ((M.supportIn T hunimod eW).weightSupport (A.val '' normalizedPolarTemplates K ε 2))
      βtarget)
    (hS : ∀ n v, S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv
      (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)) v)))
    (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
    (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
    (hbridge : ∀ᶠ n in atTop, ∀ y : Y n,
      dist (F.inclusionN (coneProbeSecond (S n).toMulEquiv (base n)
          (y.val.2 : F.N.carrier) ((S n).symm (step n))) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (base n * S n ((y.val.2 : F.N.carrier) * σ y.val.1)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
    (actionQ : F.D.carrier →* MulAut Dt.Q.carrier) (act : G →* Equiv.Perm Dt.Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q =
      Dt.maps.quotient u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : ((μN).prod νD) cell ≠ 0) (hcelltop : ((μN).prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions Dt.maps.quotient μQ μI νD scale P₂,
        μN = Measure.map (quotientSectionHomeomorph Dt.maps.quotient Dt.maps.quotient_continuous
          R.sectionMap R.section_rightInverse).symm ((μQ).prod μI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 0)
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ)
    (hHaar : ∀ (g : G) (E : Set Dt.Q.carrier), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μQ E) :
    ell (bval true - bval false) ≤ 0 := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
