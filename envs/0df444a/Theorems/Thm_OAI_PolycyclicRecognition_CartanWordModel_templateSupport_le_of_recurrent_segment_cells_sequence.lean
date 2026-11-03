-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_templateSupport_le_of_recurrent_segment_cells_sequence
-- name    : OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-02T18:03:54.025089+00:00
-- url     : https://prove2.me/theorems/23ee2141-b507-428e-ac87-b2636c734798
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentCellPacking.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentCellPacking.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set`, `open scoped Manifold NNReal ENNReal Topology`):
--
--   ```lean
--   theorem templateSupport_le_of_recurrent_segment_cells_sequence
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (X : I → H) (SD : Finset (FreeMagma I)) (βD : WordBasisSelections X SD)
--       (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ : ℝ} (hT₀ : 0 < T₀)
--       (source : Set W)
--       (hsource : source = segment ℝ
--         (eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
--           GroupLieAlgebra (𝓘(ℝ, EG)) G)))
--         ((eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
--           GroupLieAlgebra (𝓘(ℝ, EG)) G))) +
--           T₀ • eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
--       (β : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW source) β.val)
--       (x : ℕ → G)
--       (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
--       (D : ℕ → ℕ → ℝ)
--       (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
--       (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
--       {m c : ℕ} (aN : DynkinCoefficients c 2)
--       (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
--       (letters : Fin m → Fin M.letterCount)
--       (sample : ℕ → ℕ → ℝ → F.N.carrier)
--       (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
--       (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
--         F.ExpN (F.N.equiv (u • (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source (letters j)) • M.letter (letters j)))))
--       (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
--         (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
--         (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
--         (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
--       (hS : IsCompact S)
--       (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
--         fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
--           (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i)) ∈ S)
--       (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
--         (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
--         (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
--         (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
--       (hb₁ : b₁ ∈ S)
--       (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
--         fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
--           (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i))) atTop (𝓝 b₁))
--       (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
--       (honto : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters b₁) t₀))
--       (σ : ℕ → ℕ → Measure F.N.carrier) [∀ r j, IsProbabilityMeasure (σ r j)]
--       (hlaw : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
--       (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
--       (hK₀ : ∀ r j, ∀ᵐ u ∂σ r j, u ∈ K₀ r j)
--       (hRfin : ∀ r j, μ (R₀ r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R₀ r j)).toReal)
--       (hQR : ∀ r j, ∀ u ∈ Q r, ∀ v ∈ K₀ r j, u * v ∈ R₀ r j)
--       (hD : ∀ r j, 0 < D r j)
--       (hdenom : ∀ r j, (μ (R₀ r j)).toReal ≤ D r j * (μ (Q r)).toReal)
--       (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
--       (hApos : ∀ r, 0 < (μ (A r)).toReal)
--       (hAlower : HasSubexponentialLowerBoundSeq scale
--         (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
--       (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j))
--       (g : ℝ → W) (hg : Continuous g)
--       (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
--       (hgood : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ t ∈ Icc 0 T₀,
--         ‖(π ((f r).val.1 ((x r * F.inclusionN u *
--           F.inclusionD (F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale r) z)))) *
--             F.inclusionD (F.ExpD (F.D.equiv ((scale r * t) • v)))))).toAdd -
--           center r - scale r • g t‖ ≤ scale r * (ζ r + η)) :
--       (M.supportIn T hunimod eW).templateSupport source ≤
--         (M.supportIn T hunimod eW).templateSupport (g '' Icc 0 T₀)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport`, `OAI.PolycyclicRecognition.WordBasisSelections.basis` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.basisBracket` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.HasSubexponentialLowerBoundSeq` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.uniformIntervalLaw` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.SupportDatum.templateSupport` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.differenceAmplitudeWordEndpoint` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.wordChartPivot` (definitions bundle `OAIQ093D011` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentCellPacking.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009
import Definitions.Def_OAIQ093D011

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal Topology

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
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
include hπExp dynkinN dynkinD haarN haarD in
theorem templateSupport_le_of_recurrent_segment_cells_sequence
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (X : I → H) (SD : Finset (FreeMagma I)) (βD : WordBasisSelections X SD)
    (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (source : Set W)
    (hsource : source = segment ℝ
      (eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      ((eW (heightProjection T.character ((WordBasisSelections.basis X SD βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) +
        T₀ • eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (x : ℕ → G)
    (A Q : ℕ → Set F.N.carrier) (K₀ R₀ : ℕ → ℕ → Set F.N.carrier)
    (D : ℕ → ℕ → ℝ)
    (μ : Measure F.N.carrier) [SFinite μ] [μ.IsMulRightInvariant]
    (f : ℕ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g => (π g).toAdd))
    {m c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ u v, F.ExpN (finiteDynkinPolynomial aN ![u, v]) = F.ExpN u * F.ExpN v)
    (letters : Fin m → Fin M.letterCount)
    (sample : ℕ → ℕ → ℝ → F.N.carrier)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      F.ExpN (F.N.equiv (u • (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source (letters j)) • M.letter (letters j)))))
    (S : Set (((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)))
    (hS : IsCompact S)
    (hb : ∀ r, (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i)) ∈ S)
    (b₁ : ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →L[ℝ]
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) ×
      (Fin M.letterCount → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hb₁ : b₁ ∈ S)
    (hlim : Tendsto (fun r => (basisBracket (M.boxBasis T hunimod eW source β (scale r)),
      fun i => (M.boxBasis T hunimod eW source β (scale r)).equivFun
        (Real.exp (scale r * (M.supportIn T hunimod eW).weightSupport source i) • M.letter i))) atTop (𝓝 b₁))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (ρ : ℝ) (hρ : 1 ≤ ρ) (t₀ : Fin (m + m) → ℝ) (ht₀ : ‖t₀‖ ≤ ρ)
    (honto : Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters b₁) t₀))
    (σ : ℕ → ℕ → Measure F.N.carrier) [∀ r j, IsProbabilityMeasure (σ r j)]
    (hlaw : ∀ r j, MeasurePreserving (sample r j) (uniformIntervalLaw ρ) (σ r j))
    (hQfin : ∀ r, μ (Q r) ≠ ∞) (hQpos : ∀ r, 0 < (μ (Q r)).toReal)
    (hK₀ : ∀ r j, ∀ᵐ u ∂σ r j, u ∈ K₀ r j)
    (hRfin : ∀ r j, μ (R₀ r j) ≠ ∞) (hRpos : ∀ r j, 0 < (μ (R₀ r j)).toReal)
    (hQR : ∀ r j, ∀ u ∈ Q r, ∀ v ∈ K₀ r j, u * v ∈ R₀ r j)
    (hD : ∀ r j, 0 < D r j)
    (hdenom : ∀ r j, (μ (R₀ r j)).toReal ≤ D r j * (μ (Q r)).toReal)
    (hA : ∀ r, MeasurableSet (A r)) (hAQ : ∀ r, A r ⊆ Q r)
    (hApos : ∀ r, 0 < (μ (A r)).toReal)
    (hAlower : HasSubexponentialLowerBoundSeq scale
      (fun r => (μ (A r)).toReal / (μ (Q r)).toReal))
    (hDupper : ∀ j, j < m → HasSubexponentialUpperBoundSeq scale (fun r => D r j))
    (g : ℝ → W) (hg : Continuous g)
    (center : ℕ → W) (ζ : ℕ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    (hgood : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ t ∈ Icc 0 T₀,
      ‖(π ((f r).val.1 ((x r * F.inclusionN u *
        F.inclusionD (F.ExpD (F.D.equiv (wordChartPivot X SD βD (scale r) z)))) *
          F.inclusionD (F.ExpD (F.D.equiv ((scale r * t) • v)))))).toAdd -
        center r - scale r • g t‖ ≤ scale r * (ζ r + η)) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport (g '' Icc 0 T₀) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
