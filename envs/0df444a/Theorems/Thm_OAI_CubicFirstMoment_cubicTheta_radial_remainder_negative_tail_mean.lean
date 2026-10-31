-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_radial_remainder_negative_tail_mean
-- name    : OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:48:30.356957+00:00
-- url     : https://prove2.me/theorems/01a0c465-04c1-419a-886d-78b387698c3b
-- title:
--   OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialNegativeTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialNegativeTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem cubicTheta_radial_remainder_negative_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
--       (W : ℝ→ℂ) (hW : HasCompactSupport W)
--       (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
--       {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
--       (hm : AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-A))
--       (hp : AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-A))
--       (htail : ∀ t : ℝ, |t|≤2*T →
--         ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
--           (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
--       (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r W X (-t)‖)/T≤
--         81*((∫ t in T..2*T,‖metaplecticPrefactor r 0*
--           ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
--             (fun x => W x*mellinPhase (-t) x) A (X/729) nd‖)/T+
--           ‖metaplecticPrefactor r 0‖*E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.mellinPhase` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.MetaplecticDualArgument` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.PrimaryArgument` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.metaplecticPrefactor` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.metaplecticDualBall`, `OAI.CubicFirstMoment.metaplecticDualTerm` and `OAI.CubicFirstMoment.metaplecticFarTailTerm` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.cubicThetaCoreCoefficient` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.cubicThetaRadialHeightRemainder` (definitions bundle `OAIQ096A023` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialNegativeTail.lean (declaration OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A023

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicTheta_radial_remainder_negative_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-A))
    (htail : ∀ t : ℝ, |t|≤2*T →
      ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
    (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r W X (-t)‖)/T≤
      81*((∫ t in T..2*T,‖metaplecticPrefactor r 0*
        ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase (-t) x) A (X/729) nd‖)/T+
        ‖metaplecticPrefactor r 0‖*E) := by
  sorry

end CubicFirstMoment

end

end OAI
end
