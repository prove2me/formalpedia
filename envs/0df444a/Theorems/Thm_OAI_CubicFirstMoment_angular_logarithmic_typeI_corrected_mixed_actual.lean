-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_logarithmic_typeI_corrected_mixed_actual
-- name    : OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:18:49.620979+00:00
-- url     : https://prove2.me/theorems/562cd104-99f2-4345-9c48-28dd954a2148
-- title:
--   OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularTypeIMixedLogSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularTypeIMixedLogSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_logarithmic_typeI_corrected_mixed_actual
--       {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
--       (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
--       {R₀ : ℝ} (hR₀ : 1 ≤ R₀)
--       (hlo : ∀ j i x, x < 1 → W j i x = 0) (hhi : ∀ j i x, R₀ < x → W j i x = 0)
--       (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Set.Ioi 0)
--       (hVs : ContDiff ℝ ∞ V)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k : ℕ) :
--       ∃ K T₀ : ℝ, 0 < K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein) (t A : ℝ),
--         T₀ ≤ L j → 1 ≤ L j → (∀ i, 1 ≤ Xi i) → (∏ i, Xi i) = L j → L j^(99/100:ℝ) ≤ A →
--         let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
--         let β := angularHeightPrimeCoefficient ℓ R₀ (W j) Xi
--         ‖((cStar:ℂ)*star (dispersionModel S β t))*
--           ((∑ b ∈ S, β b*normTwist t b*typeIMixedGauss b V A)-mixedMassModel S β t V A)‖ ≤
--           K*A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.normTwist` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.dispersionModel` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.angularHeightPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.mixedMassModel` and `OAI.CubicFirstMoment.typeIMixedGauss` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.cStar` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularTypeIMixedLogSaving.lean (declaration OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_logarithmic_typeI_corrected_mixed_actual
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀)
    (hlo : ∀ j i x, x < 1 → W j i x = 0) (hhi : ∀ j i x, R₀ < x → W j i x = 0)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Set.Ioi 0)
    (hVs : ContDiff ℝ ∞ V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k : ℕ) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein) (t A : ℝ),
      T₀ ≤ L j → 1 ≤ L j → (∀ i, 1 ≤ Xi i) → (∏ i, Xi i) = L j → L j^(99/100:ℝ) ≤ A →
      let S := fullSquarefreePrimeSupport R₀ (W j) Xi e
      let β := angularHeightPrimeCoefficient ℓ R₀ (W j) Xi
      ‖((cStar:ℂ)*star (dispersionModel S β t))*
        ((∑ b ∈ S, β b*normTwist t b*typeIMixedGauss b V A)-mixedMassModel S β t V A)‖ ≤
        K*A^(2/3:ℝ)*(L j)^(5/3:ℝ)/(1+Real.log (L j))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
