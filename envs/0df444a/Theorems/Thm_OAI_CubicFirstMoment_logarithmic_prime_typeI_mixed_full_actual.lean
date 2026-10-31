-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_logarithmic_prime_typeI_mixed_full_actual
-- name    : OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:26:32.310113+00:00
-- url     : https://prove2.me/theorems/31dc21cf-d040-4e7d-9e99-be676e0999f9
-- title:
--   OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralTypeIMixedFull.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralTypeIMixedFull.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem logarithmic_prime_typeI_mixed_full_actual
--       {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
--       (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
--       {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       {B R₀ : ℝ} (hB : 1 ≤ B) (J : ℕ) (hJ : R₀^Fintype.card ι < (2:ℝ)^J) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein)
--         (w : Eisenstein → δ) (t U : ℝ),
--         1 ≤ L j → (∀ i, 0 < Xi i) → (∏ i, Xi i) = L j →
--         (∀ i x, x < 1 → W j i x = 0) → (∀ i x, R₀ < x → W j i x = 0) →
--         1 ≤ U → 2 ≤ L j*U → B ≤ L j*U → (2:ℝ)^J*L j ≤ (L j*U)^(51/100:ℝ) →
--         (∀ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e, ∀ x : ℝ, B < x → V (w r) x = 0) →
--         let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
--         ‖∑ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e,
--             β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
--           K*U^(-1/6:ℝ)*(L j*U)^(5/6-1/100:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.normTwist` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.LogarithmicWeightFamily` and `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.fullPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.typeIMixedGauss` and `OAI.CubicFirstMoment.typeIMixedModel` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.full_prime_centered_product_bilinear_actual`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual` and `OAI.CubicFirstMoment.semiprime_block_log_saving_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralTypeIMixedFull.lean (declaration OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_prime_typeI_mixed_full_actual
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B R₀ : ℝ} (hB : 1 ≤ B) (J : ℕ) (hJ : R₀^Fintype.card ι < (2:ℝ)^J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (e : Eisenstein)
      (w : Eisenstein → δ) (t U : ℝ),
      1 ≤ L j → (∀ i, 0 < Xi i) → (∏ i, Xi i) = L j →
      (∀ i x, x < 1 → W j i x = 0) → (∀ i x, R₀ < x → W j i x = 0) →
      1 ≤ U → 2 ≤ L j*U → B ≤ L j*U → (2:ℝ)^J*L j ≤ (L j*U)^(51/100:ℝ) →
      (∀ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e, ∀ x : ℝ, B < x → V (w r) x = 0) →
      let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
      ‖∑ r ∈ fullSquarefreePrimeSupport R₀ (W j) Xi e,
          β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*(L j*U)^(5/6-1/100:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
