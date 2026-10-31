-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_completed_negative_tail_mean
-- name    : OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:38:35.311976+00:00
-- url     : https://prove2.me/theorems/ef07f11e-9e29-4bae-bb0c-74d0151b966c
-- title:
--   OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaNegativeTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaNegativeTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem cubicTheta_completed_negative_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
--       {ℓ : ℤ} (hℓ : ℓ≠0) (W : ℝ→ℂ) (hW : HasCompactSupport W)
--       (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
--       {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
--       (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
--       (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
--       (htail : ∀ t : ℝ, |t|≤2*T →
--         ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r ℓ
--           (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
--       (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ W X (-t)‖)/T≤
--         81*((∫ t in T..2*T,‖metaplecticPrefactor r ℓ*
--           ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ
--             (fun x => W x*mellinPhase (-t) x) A (X/729) nd‖)/T+
--           ‖metaplecticPrefactor r ℓ‖*E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.mellinPhase` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.MetaplecticDualArgument` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.PrimaryArgument` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.metaplecticHeightCompleted` and `OAI.CubicFirstMoment.metaplecticPrefactor` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.metaplecticDualBall`, `OAI.CubicFirstMoment.metaplecticDualTerm` and `OAI.CubicFirstMoment.metaplecticFarTailTerm` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.cubicThetaCoreCoefficient` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaNegativeTail.lean (declaration OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicTheta_completed_negative_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    {ℓ : ℤ} (hℓ : ℓ≠0) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (htail : ∀ t : ℝ, |t|≤2*T →
      ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r ℓ
        (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
    (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ W X (-t)‖)/T≤
      81*((∫ t in T..2*T,‖metaplecticPrefactor r ℓ*
        ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ
          (fun x => W x*mellinPhase (-t) x) A (X/729) nd‖)/T+
        ‖metaplecticPrefactor r ℓ‖*E) := by
  sorry

end CubicFirstMoment

end

end OAI
end
