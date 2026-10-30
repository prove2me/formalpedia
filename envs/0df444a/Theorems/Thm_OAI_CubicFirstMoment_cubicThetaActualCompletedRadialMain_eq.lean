-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaActualCompletedRadialMain_eq
-- name    : OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:36:53.873022+00:00
-- url     : https://prove2.me/theorems/d0bc4146-dcb5-4669-9417-3682010fb039
-- title:
--   OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCenteredLow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCenteredLow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`):
--
--   ```lean
--   lemma cubicThetaActualCompletedRadialMain_eq {r : Eisenstein} (hr : primary r)
--       (W : ℝ → ℂ) {X : ℝ} (hX : 0<X) :
--       cubicThetaActualCompletedRadialMain r W X=metaplecticMain r 0 W X
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.metaplecticMain` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain` (definitions bundle `OAIQ096A016` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCenteredLow.lean (declaration OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A010
import Definitions.Def_OAIQ096A016

section

attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CubicFirstMoment

lemma cubicThetaActualCompletedRadialMain_eq {r : Eisenstein} (hr : primary r)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X=metaplecticMain r 0 W X := by
  sorry

end CubicFirstMoment

end

end OAI
end
