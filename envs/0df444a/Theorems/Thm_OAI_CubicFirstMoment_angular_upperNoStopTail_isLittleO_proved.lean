-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_upperNoStopTail_isLittleO_proved
-- name    : OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:22:55.215918+00:00
-- url     : https://prove2.me/theorems/0c74637f-f677-46ee-93c0-0bd293b1c0b4
-- title:
--   OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaUpperNoStopNegligible.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaUpperNoStopNegligible.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Asymptotics`, `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_upperNoStopTail_isLittleO_proved (hℓ : ℓ ≠ 0) (m : ℕ) (hpnt : PrimaryPrimePNT)
--       {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
--       {κ η cap : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/12)
--       (hη : 0 < η) (hηκ : η ≤ κ/4) (hcap : 1 < cap) :
--       ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (ξ : ℝ)
--         (H T : ℝ → ℝ),
--         (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+η/2) ∧ Real.log X ≤ T X) →
--         (fun X => angular_upperNoStopTail ℓ m κ ρ ξ (H X) (T X) X)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angular_upperNoStopTail` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaUpperNoStopNegligible.lean (declaration OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved)

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
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_upperNoStopTail_isLittleO_proved (hℓ : ℓ ≠ 0) (m : ℕ) (hpnt : PrimaryPrimePNT)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {κ η cap : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/12)
    (hη : 0 < η) (hηκ : η ≤ κ/4) (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ (ξ : ℝ)
      (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+η/2) ∧ Real.log X ≤ T X) →
      (fun X => angular_upperNoStopTail ℓ m κ ρ ξ (H X) (T X) X)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
