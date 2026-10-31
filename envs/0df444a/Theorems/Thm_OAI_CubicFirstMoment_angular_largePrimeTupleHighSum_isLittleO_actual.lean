-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_largePrimeTupleHighSum_isLittleO_actual
-- name    : OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:19:31.477867+00:00
-- url     : https://prove2.me/theorems/612fa310-c636-4e65-9d02-57fabb55b5cd
-- title:
--   OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleHighSum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleHighSum.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_largePrimeTupleHighSum_isLittleO_actual (i j : ℕ)
--       (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
--       (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
--       (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` and `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_primeProductLowHeight_sub_low_scale_isLittleO_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleHighSum.lean (declaration OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual)

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
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_largePrimeTupleHighSum_isLittleO_actual (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) (hδ1 : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => angular_largePrimeTupleHighSum ℓ i j ξ Ct (H X) X) =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
