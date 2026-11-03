-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_eventually_root_neighbor_labels_eq_m
-- name    : OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq_m
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T23:13:57.979505+00:00
-- url     : https://prove2.me/theorems/6f4b2a7b-d20d-4b1c-a848-2306500925bb
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq_m: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanEventualNeighborLabels.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanEventualNeighborLabels.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set`, `open scoped Manifold Topology ENNReal NNReal`):
--
--   ```lean
--   theorem eventually_root_neighbor_labels_eq_m
--       (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (rem : RemezPolynomialInput)
--       (π : G →* Multiplicative W) {Kπ : ℝ≥0}
--       (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
--       (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ x, chartN x = F.ExpN x)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ x, chartD x = F.ExpD x)
--       (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--
--       (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
--       (hint : (interior cell).Nonempty)
--       (pivot : Fin M.letterCount → H)
--       (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ cell)
--       (mode : ℕ → Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
--       (hpoly : cell = {w | ∀ j, α j w ≤ c j})
--       (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
--         ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
--       (A₁ A₂ : ℕ → templateSymmetryGroup (M.supportIn T hunimod eW))
--       (βcell : M.Bases)
--       (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW cell) βcell.val)
--       (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
--       (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
--       (βD : WordBasisSelections X (boundedBracketWords d))
--       (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
--         (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
--
--       {cN : ℕ} (aN : DynkinCoefficients cN 2)
--       (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (scale : ℕ → ℕ → ℝ) (hscale : ∀ j, Tendsto (scale j) atTop atTop)
--       (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
--       (p : ℕ → ℕ → NormalizedPair G Λ) (x : ℕ → ℕ → G)
--       (R : ℕ → ℕ → ℝ) (k₀ k : ℕ → ℕ → F.N.carrier) (η δ : ℕ → ℝ)
--       (t : ℕ → ℕ → ℝ) (β : ℕ → ℕ → M.Bases)
--       (hR0 : ∀ j n, 0 ≤ R j n)
--       (hR : ∀ j, HasSubexponentialUpperBoundSeq (scale j) (R j))
--       (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
--       (hk₀ : ∀ j n, k₀ j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
--       (hk : ∀ j n, k j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--         ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
--       (hη : Tendsto η atTop (𝓝 0))
--       (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight (mode j) (pivot (mode j)) + η j) * scale j n))
--       (hstep : ∀ j n, F.inclusionN (k j n) =
--         ExpG (t j n • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
--       (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
--       [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
--       (profile : ℕ → ℕ → F.N.carrier → S × S) (hp : ∀ j n, Measurable (profile j n))
--       (hactual : ∀ j n q, q ∈ (fun y => y * k₀ j n) ''
--         M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1 → ∀ z,
--         let b := WordBasisSelections.basis X (boundedBracketWords d) βD
--         let br := exponentialRescaleBasis b
--           (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale j n))
--         (profile j n q).1.val z = rescaledMapProfile
--           (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN q)
--           (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
--         (profile j n q).2.val z = rescaledMapProfile
--           (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN (q * k j n))
--           (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z)
--       (ν : ℕ → ProbabilityMeasure (S × S))
--       (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
--         (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
--           cell βcell (scale j n) (k₀ j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ν j)))
--       (f : ℕ → S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support) (b₁ b₂ : ℕ → W) (shrink : ℝ)
--       (haff₁ : ∀ j z, eW (heightProjection T.character
--         ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--           GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = (A₁ j).val (eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
--       (haff₂ : ∀ j z, eW (heightProjection T.character
--         ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--           GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = (A₂ j).val (eW (heightProjection T.character
--           ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
--             GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : (∀ᶠ j in atTop, A₁ j = A₂ j)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.NormalizedPair` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.templateSymmetryGroup`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.CartanWordModel.translatedGroupBoxProbability` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold_m` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanEventualNeighborLabels.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

variable [Fintype I] [DecidableEq I] {J : Type} [Fintype J]

set_option maxHeartbeats 1000000 in
theorem eventually_root_neighbor_labels_eq_m
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) {Kπ : ℝ≥0}
    (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))

    (cell : Set W) (hcell : IsCompact cell) (hconv : Convex ℝ cell)
    (hint : (interior cell).Nonempty)
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ cell)
    (mode : ℕ → Fin M.letterCount) (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ)
    (hpoly : cell = {w | ∀ j, α j w ≤ c j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = c j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (A₁ A₂ : ℕ → templateSymmetryGroup (M.supportIn T hunimod eW))
    (βcell : M.Bases)
    (hβcell : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW cell) βcell.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)

    {cN : ℕ} (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale : ℕ → ℕ → ℝ) (hscale : ∀ j, Tendsto (scale j) atTop atTop)
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ))
    (p : ℕ → ℕ → NormalizedPair G Λ) (x : ℕ → ℕ → G)
    (R : ℕ → ℕ → ℝ) (k₀ k : ℕ → ℕ → F.N.carrier) (η δ : ℕ → ℝ)
    (t : ℕ → ℕ → ℝ) (β : ℕ → ℕ → M.Bases)
    (hR0 : ∀ j n, 0 ≤ R j n)
    (hR : ∀ j, HasSubexponentialUpperBoundSeq (scale j) (R j))
    (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (hk₀ : ∀ j n, k₀ j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hk : ∀ j n, k j n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ j) • w) '' cell) (β j n) (scale j n) (R j n))
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ j n, |t j n| ≤ R j n * Real.exp ((M.weight (mode j) (pivot (mode j)) + η j) * scale j n))
    (hstep : ∀ j n, F.inclusionN (k j n) =
      ExpG (t j n • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (profile : ℕ → ℕ → F.N.carrier → S × S) (hp : ∀ j n, Measurable (profile j n))
    (hactual : ∀ j n q, q ∈ (fun y => y * k₀ j n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale j n) 1 → ∀ z,
      let b := WordBasisSelections.basis X (boundedBracketWords d) βD
      let br := exponentialRescaleBasis b
        (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale j n))
      (profile j n q).1.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN q)
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
      (profile j n q).2.val z = rescaledMapProfile
        (fun g => (π ((p j n).val.1 g)).toAdd) (x j n) (F.inclusionN (q * k j n))
        (Real.log (scale j n)) (fun z => ExpG (br.equivFun.symm z)) z)
    (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (scale j n) (k₀ j n)) (f := (profile j n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support) (b₁ b₂ : ℕ → W) (shrink : ℝ)
    (haff₁ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).1.val z = (A₁ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ j)
    (haff₂ : ∀ j z, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ j) • w) '' interior cell → (f j).2.val z = (A₂ j).val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ j) : (∀ᶠ j in atTop, A₁ j = A₂ j) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
