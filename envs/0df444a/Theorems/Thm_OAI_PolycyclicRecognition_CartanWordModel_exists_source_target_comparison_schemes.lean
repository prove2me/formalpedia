-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_source_target_comparison_schemes
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:39:25.743587+00:00
-- url     : https://prove2.me/theorems/f2a164bd-5224-4858-ba00-ae73e4266efb
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanComparisonSchemes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanComparisonSchemes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra Filter Set`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_source_target_comparison_schemes
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       {c : ℕ} (aN : DynkinCoefficients c 2)
--       (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
--       (E E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
--       (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
--       (β β₁ β₂ γ : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
--         (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val)
--       (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
--         (M.boxCost T hunimod eW E₁) β₁.val)
--       (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
--         (M.boxCost T hunimod eW E₂) β₂.val)
--       (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
--         (M.boxCost T hunimod eW E) γ.val)
--       (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n)
--       (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H)) :
--       ∃ u : ℕ → ℕ, StrictMono u ∧ ∃ h : ℕ, 0 < h ∧
--         ∃ (target : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
--           (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
--             (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)),
--           Tendsto (fun n =>
--             let bU := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale (u n))
--             let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale (u n))
--             let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale (u n))
--             (basisBracket bU, boxCoordinateChange bU b₁, boxCoordinateChange bU b₂))
--             atTop (𝓝 target) ∧
--           Function.Surjective (fderiv ℝ
--             (alternatingCoordinateProduct aN target.1 target.2.1 target.2.2) z₀) ∧
--           ∃ (m : ℕ) (letters : Fin m → Fin M.letterCount)
--             (source : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
--             (t₀ : Fin (m + m) → ℝ),
--             Tendsto (fun n =>
--               let bS := M.boxBasis T hunimod eW E γ (scale (u n))
--               (basisBracket bS, fun i => bS.equivFun
--                 (Real.exp (scale (u n) * (M.supportIn T hunimod eW).weightSupport E i) • M.letter i)))
--               atTop (𝓝 source) ∧
--             Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters source) t₀)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.AlternatingLawData`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.basisBracket` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.WordLawData` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.boxCoordinateChange` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.finiteDynkinPolynomial` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.alternatingCoordinateProduct` and `OAI.PolycyclicRecognition.differenceAmplitudeWordEndpoint` (definitions bundle `OAIQ093D009` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanComparisonSchemes.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_source_target_comparison_schemes
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β β₁ β₂ γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E) γ.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n)
    (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∃ h : ℕ, 0 < h ∧
      ∃ (target : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
        (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
          (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)),
        Tendsto (fun n =>
          let bU := M.boxBasis T hunimod eW (E₁ ∪ E₂) β (scale (u n))
          let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale (u n))
          let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale (u n))
          (basisBracket bU, boxCoordinateChange bU b₁, boxCoordinateChange bU b₂))
          atTop (𝓝 target) ∧
        Function.Surjective (fderiv ℝ
          (alternatingCoordinateProduct aN target.1 target.2.1 target.2.2) z₀) ∧
        ∃ (m : ℕ) (letters : Fin m → Fin M.letterCount)
          (source : WordLawData (Fin M.letterCount) (finrank ℝ (cartanRootIdeal H)))
          (t₀ : Fin (m + m) → ℝ),
          Tendsto (fun n =>
            let bS := M.boxBasis T hunimod eW E γ (scale (u n))
            (basisBracket bS, fun i => bS.equivFun
              (Real.exp (scale (u n) * (M.supportIn T hunimod eW).weightSupport E i) • M.letter i)))
            atTop (𝓝 source) ∧
          Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint aN letters source) t₀) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
