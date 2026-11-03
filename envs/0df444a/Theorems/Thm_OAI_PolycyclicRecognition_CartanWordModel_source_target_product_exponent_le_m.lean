-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_source_target_product_exponent_le_m
-- name    : OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le_m
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T23:14:52.958098+00:00
-- url     : https://prove2.me/theorems/a843f437-ebf9-4672-a8a6-c1cc93d4159d
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le_m: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSourceTargetComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSourceTargetComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra MeasureTheory Filter Set`, `open scoped Manifold Topology ENNReal NNReal`):
--
--   ```lean
--   theorem source_target_product_exponent_le_m
--       (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (rem : RemezPolynomialInput)
--       (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
--       (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
--       {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
--       (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
--       (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
--       (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
--       (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
--       (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
--       (hlim : Tendsto (fun n =>
--         let b := M.boxBasis T hunimod eW E β (scale n)
--         let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
--         let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
--         (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
--       (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
--         (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
--       (hsub : Function.Surjective
--         (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
--       (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
--       (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E₁) β₁.val)
--       (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E₂) β₂.val)
--       (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
--       (s : ℕ → Finset (Fin (h * 2) → G))
--       (htarget : ∀ᶠ n in atTop, ∀ x, x ∈ s n →
--         ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
--             ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
--           (∀ i, PathMetricBound (path i) (A * scale n)
--             (B * (1 + Real.log (2 + scale n)))) ∧
--           (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
--             ‖(π (path i u)).toAdd - scale n • z‖ ≤
--               2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
--           ∀ i : Fin (h * 2),
--             ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
--               η n * scale n)
--       (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
--       (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
--         Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
--           (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
--       (Esrc : Set W) (hEsrc : IsCompact Esrc) (hne : Esrc.Nonempty)
--       (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
--       {Cs bs : ℝ} (hCs : 0 ≤ Cs)
--       (hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ S n,
--         ∃ path : Path (1 : G) z,
--           PathMetricBound path (Cs * scale n) (Cs * (1 + Real.log (2 + scale n))) ∧
--           ∀ t, ∃ w ∈ Esrc, ‖(π (path t)).toAdd - scale n • w‖ ≤
--             ε * scale n + bs * (1 + Real.log (2 + scale n)))
--       {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G)
--       (hterminal : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ z ∈ S n,
--         x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩ = (p n).val.1 (base n * z)) :
--       columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤
--         (M.supportIn T hunimod eW).templateSupport Esrc
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.AlternatingLawData`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.columnBasisWeight`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.basisBracket` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.HasSubexponentialLowerBoundSeq`, `OAI.PolycyclicRecognition.PathMetricBound` and `OAI.PolycyclicRecognition.RemezPolynomialInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.basedTuplePosition` and `OAI.PolycyclicRecognition.boxCoordinateChange` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.alternatingCoordinateFamily`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn` and `OAI.PolycyclicRecognition.SupportDatum.templateSupport` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.alternatingCoordinateProduct` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le_m` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSourceTargetComparison.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
theorem source_target_product_exponent_le_m
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (htarget : ∀ᶠ n in atTop, ∀ x, x ∈ s n →
      ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
          ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
        (∀ i, PathMetricBound (path i) (A * scale n)
          (B * (1 + Real.log (2 + scale n)))) ∧
        (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
          ‖(π (path i u)).toAdd - scale n • z‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
        ∀ i : Fin (h * 2),
          ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
            η n * scale n)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (Esrc : Set W) (hEsrc : IsCompact Esrc) (hne : Esrc.Nonempty)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {Cs bs : ℝ} (hCs : 0 ≤ Cs)
    (hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ S n,
      ∃ path : Path (1 : G) z,
        PathMetricBound path (Cs * scale n) (Cs * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ Esrc, ‖(π (path t)).toAdd - scale n • w‖ ≤
          ε * scale n + bs * (1 + Real.log (2 + scale n)))
    {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G)
    (hterminal : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ z ∈ S n,
      x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩ = (p n).val.1 (base n * z)) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤
      (M.supportIn T hunimod eW).templateSupport Esrc := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
