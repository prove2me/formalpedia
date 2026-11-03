-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_original_neighbor_offset_nonpos
-- name    : OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:30:49.436337+00:00
-- url     : https://prove2.me/theorems/4226eabe-3806-4a89-8914-008263aa36b5
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOriginalNeighborOffset.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOriginalNeighborOffset.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace`, `open scoped Manifold Topology NNReal ENNReal`):
--
--   ```lean
--   theorem original_neighbor_offset_nonpos
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
--       (probe : Fin 3 → ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
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
--         ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ v, chartN v = F.ExpN v)
--       (baseGroup step : ℕ → F.N.carrier)
--       (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
--       (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
--       (S : Set C((Fin (finrank ℝ H) → ℝ), W))
--       [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
--       (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
--       (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
--         (fun v => v * baseGroup n * step n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
--         (profile n q).val z = rescaledMapProfile
--           (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
--           (max (Real.log (scale n)) 0)
--           (F.profileChart (exponentialRescaleBasis
--             (WordBasisSelections.basis X (boundedBracketWords d) βD)
--             (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
--             (max (Real.log (scale n)) 0))) z)
--       (law : ProbabilityMeasure (S × S))
--       (hlaw : Tendsto (fun n => ProbabilityMeasure.map
--         (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
--           E β (scale n) (baseGroup n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
--         atTop (𝓝 law))
--       (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
--       (hf : f ∈ (law : Measure (S × S)).support)
--       (haffine : ∀ s z,
--         eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
--         (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
--       (hπS : Continuous πS) (σS : C(QS, F.N.carrier))
--       (hσS : ∀ q, πS (σS q) = q)
--       (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure F.N.carrier)
--       [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
--       [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
--       (hφS : ∀ d, MeasurePreserving (F.action d) μS μS)
--       (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σS hσS).symm
--         (μQS.prod μIS))
--       (flow : ℕ → F.N.carrier ≃ₜ F.N.carrier)
--       (hflow : ∀ n, MeasurePreserving (flow n) μS μS)
--       (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
--       (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
--       (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
--       (hregular : ∀ n,
--         (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
--           (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
--           (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
--             Measure (ZQ ×ˢ J n)).InnerRegular)
--       (P₁ P₂ : ℝ) {v : ℝ} (hv : 0 < v)
--       (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
--       (tiles : ℕ → ℕ) (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
--       (anchorRoot : ∀ n, Fin (tiles n) → F.N.carrier)
--       (secondRoot : ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
--       (hfirst : ∀ n y, F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length))) =
--         baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1))
--       (hanchor : ∀ n y, F.ExpN (F.N.equiv (D.vertex 1 n y (Fin.last (P 1).length))) =
--         anchorRoot n (tile n y))
--       (hsecond : ∀ n y, F.ExpN (F.N.equiv (D.vertex 2 n y (Fin.last (P 2).length))) =
--         secondRoot n y)
--       (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
--       (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
--       (hbridge : ∀ᶠ n in atTop, ∀ y : ZQ ×ˢ J n,
--         dist (F.inclusionN (secondRoot n y) * Exp (scale n •
--             (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
--           (F.inclusionN (baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1)) *
--             Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
--       (πT : F.N.carrier →* QT) (hπT : Continuous πT)
--       (μT : Measure QT) (μTI : Measure πT.ker)
--       (μ : Measure F.N.carrier) (νD : Measure F.D.carrier)
--       [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite νD]
--       [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [νD.IsMulLeftInvariant]
--       (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
--       (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
--       (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
--       (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
--       (hcell0 : (μ.prod νD) cell ≠ 0) (hcelltop : (μ.prod νD) cell ≠ ⊤)
--       (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
--       (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
--         ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions πT μT μTI νD scale P₂,
--           μ = Measure.map (quotientSectionHomeomorph πT hπT
--             R.sectionMap R.section_rightInverse).symm (μT.prod μTI) ∧
--           ∀ᶠ n in atTop, R.ControlsTwoPaths
--             (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
--             π cell
--             ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 0)
--             ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 2)
--             (fun n => 2 * η n) Cp Cp δtarget n)
--       (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
--       (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
--       (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
--       (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
--         ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μT E)
--       (htiles : ∀ᶠ n in atTop,
--         (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
--       ell (bval true - bval false) ≤ 0
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanFactorModel.profileChart`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.normalizedPairAction` and `OAI.PolycyclicRecognition.quotientSectionHomeomorph` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ErgodicDecompositionInput`, `OAI.PolycyclicRecognition.ReducedCohomologyInput` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ZeroMeanL2` and `OAI.PolycyclicRecognition.stationaryL2Mean` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.CartanWordModel.translatedGroupBoxProbability` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.MeasuredProbeRegions`, `OAI.PolycyclicRecognition.cellSubtypeProbability` and `OAI.PolycyclicRecognition.MeasuredProbeRegions.ControlsTwoPaths` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.normalizedPairContinuousAction`, `OAI.PolycyclicRecognition.weightChamber` and `OAI.PolycyclicRecognition.zeroMeanL2Action` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains` and `OAI.PolycyclicRecognition.CartanWordModel.LinkedProbeChains` (definitions bundle `OAIQ093D013` of this split); `OAI.PolycyclicRecognition.normalizedPair_polishSpace`, `OAI.PolycyclicRecognition.zeroMeanL2Isometric` and `OAI.PolycyclicRecognition.zeroMeanL2SMulComm` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanOriginalNeighborOffset.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos)

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

variable [IsTopologicalGroup F.N.carrier]

variable {QS QT : Type}
  [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS] [T2Space QS]
  [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
  [Group QT] [TopologicalSpace QT] [IsTopologicalGroup QT]
  [SecondCountableTopology QT] [MeasurableSpace QT] [BorelSpace QT]
  [MeasurableMul F.D.carrier]
  (πS : F.N.carrier →* QS) (ZQ : Set QS) (J : ℕ → Set πS.ker)
  [∀ n, CompactSpace (ZQ ×ˢ J n)] [∀ n, Nonempty (ZQ ×ˢ J n)]

set_option maxHeartbeats 1000000 in
theorem original_neighbor_offset_nonpos
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
    (probe : Fin 3 → ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
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
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (baseGroup step : ℕ → F.N.carrier)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * baseGroup n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (S × S))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (baseGroup n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 law))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
    (hf : f ∈ (law : Measure (S × S)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (hπS : Continuous πS) (σS : C(QS, F.N.carrier))
    (hσS : ∀ q, πS (σS q) = q)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure F.N.carrier)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (F.action d) μS μS)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σS hσS).symm
      (μQS.prod μIS))
    (flow : ℕ → F.N.carrier ≃ₜ F.N.carrier)
    (hflow : ∀ n, MeasurePreserving (flow n) μS μS)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (hregular : ∀ n,
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)).InnerRegular)
    (P₁ P₂ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ) (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (anchorRoot : ∀ n, Fin (tiles n) → F.N.carrier)
    (secondRoot : ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
    (hfirst : ∀ n y, F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length))) =
      baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1))
    (hanchor : ∀ n y, F.ExpN (F.N.equiv (D.vertex 1 n y (Fin.last (P 1).length))) =
      anchorRoot n (tile n y))
    (hsecond : ∀ n y, F.ExpN (F.N.equiv (D.vertex 2 n y (Fin.last (P 2).length))) =
      secondRoot n y)
    (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
    (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
    (hbridge : ∀ᶠ n in atTop, ∀ y : ZQ ×ˢ J n,
      dist (F.inclusionN (secondRoot n y) * Exp (scale n •
          (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
    (πT : F.N.carrier →* QT) (hπT : Continuous πT)
    (μT : Measure QT) (μTI : Measure πT.ker)
    (μ : Measure F.N.carrier) (νD : Measure F.D.carrier)
    [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite νD]
    [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [νD.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
    (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod νD) cell ≠ 0) (hcelltop : (μ.prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions πT μT μTI νD scale P₂,
        μ = Measure.map (quotientSectionHomeomorph πT hπT
          R.sectionMap R.section_rightInverse).symm (μT.prod μTI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 0)
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μT E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (bval true - bval false) ≤ 0 := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
