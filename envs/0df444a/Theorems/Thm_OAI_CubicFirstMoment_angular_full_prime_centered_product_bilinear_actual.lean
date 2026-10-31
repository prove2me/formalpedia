-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_full_prime_centered_product_bilinear_actual
-- name    : OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:15:31.782145+00:00
-- url     : https://prove2.me/theorems/01600969-8b08-42f8-958a-c3b12f00a078
-- title:
--   OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularPrimeProductBilinear.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularPrimeProductBilinear.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_full_prime_centered_product_bilinear_actual
--       (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
--       (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
--       (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
--       (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
--       (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
--       (hAhi : ∀ r i x, R < x → WA r i x = 0)
--       (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
--       (hBhi : ∀ r i x, R < x → WB r i x = 0) (k U : ℕ) :
--       ∃ (η σ : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
--         ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u : ℝ),
--         T₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
--         (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
--         (LB r)^(1-η/16) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
--         eB ≠ 0 → norm eB ≤ (LB r)^σ → |u| ≤ (1+Real.log (LB r))^U →
--         ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
--           ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
--             fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
--               theta ℓ (x*y)*centeredGauss (x*y)*normTwist u (x*y)‖ ≤
--           K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.normTwist` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` and `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` and `OAI.CubicFirstMoment.fullPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.centeredGauss` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.theta` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_full_prime_centered_smoothed_bilinear_actual` and `OAI_CubicFirstMoment_angular_semiprime_smoothed_log_saving_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularPrimeProductBilinear.lean (declaration OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ]

theorem angular_full_prime_centered_product_bilinear_actual
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0) (k U : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u : ℝ),
      T₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/16) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      eB ≠ 0 → norm eB ≤ (LB r)^σ → |u| ≤ (1+Real.log (LB r))^U →
      ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
        ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
          fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
            theta ℓ (x*y)*centeredGauss (x*y)*normTwist u (x*y)‖ ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
