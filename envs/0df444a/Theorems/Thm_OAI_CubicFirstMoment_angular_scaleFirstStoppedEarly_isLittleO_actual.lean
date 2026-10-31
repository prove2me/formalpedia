-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_scaleFirstStoppedEarly_isLittleO_actual
-- name    : OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:20:06.298639+00:00
-- url     : https://prove2.me/theorems/57f14521-2f4f-4c90-ad53-07eadce2ed00
-- title:
--   OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularScaleFirstEarlyNegligible.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularScaleFirstEarlyNegligible.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_scaleFirstStoppedEarly_isLittleO_actual (ℓ : ℤ) (m : ℕ)
--       (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
--       {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
--       (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
--       (Ct : ℕ) :
--       ∃ G : ℕ, ∀ (H : ℝ → ℝ) (h : ℝ → ℕ),
--         (∀ᶠ X : ℝ in atTop, 0 < H X) →
--         (∀ᶠ X : ℝ in atTop,
--           geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X) →
--         (∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
--           (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X))) →
--         (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.geometricBinCount`, `OAI.CubicFirstMoment.geometricBinLower` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.primeProductWeights` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angular_scaleFirstStoppedSum` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductLowHeight_angular_isLittleO_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularScaleFirstEarlyNegligible.lean (declaration OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual)

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
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_scaleFirstStoppedEarly_isLittleO_actual (ℓ : ℤ) (m : ℕ)
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (Ct : ℕ) :
    ∃ G : ℕ, ∀ (H : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (∀ᶠ X : ℝ in atTop,
        geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X) →
      (∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X))) →
      (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
