-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_radial_remainder_negative_long_mean
-- name    : OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:47:49.947137+00:00
-- url     : https://prove2.me/theorems/3e4a0ffe-103f-4cef-bc43-2b2360cd4dd4
-- title:
--   OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialLongScale.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialLongScale.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory`):
--
--   ```lean
--   theorem UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean
--       {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
--       {ι : Type*} {W : ι→ℝ→ℂ} (h : UniformLogWeights W)
--       {η B : ℝ} (hη : 0<η) (hB : 0 ≤ B) :
--       ∃ K : ℝ,0 ≤ K ∧ ∀ i r,primary r → Squarefree r →
--         ∀ Y X T : ℝ,1 ≤ Y → 0<X → 1 ≤ T → norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
--         729*Real.sqrt (norm r)*T^2 ≤ X →
--         (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r (W i) X (-t)‖)/T ≤
--           K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.cubicThetaRadialHeightRemainder` (definitions bundle `OAIQ096A023` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_radial_mean` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialLongScale.lean (declaration OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean)

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
open MeasureTheory
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι→ℝ→ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0<η) (hB : 0 ≤ B) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ i r,primary r → Squarefree r →
      ∀ Y X T : ℝ,1 ≤ Y → 0<X → 1 ≤ T → norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      729*Real.sqrt (norm r)*T^2 ≤ X →
      (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r (W i) X (-t)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  sorry

end CubicFirstMoment

end

end OAI
end
