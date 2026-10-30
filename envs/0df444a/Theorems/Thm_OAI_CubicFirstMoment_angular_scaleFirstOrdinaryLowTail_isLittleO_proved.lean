-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_scaleFirstOrdinaryLowTail_isLittleO_proved
-- name    : OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:19:12.789718+00:00
-- url     : https://prove2.me/theorems/cfe75053-cf6a-4f10-8ede-bf393f42947e
-- title:
--   OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaOrdinaryTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaOrdinaryTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Asymptotics`, `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_scaleFirstOrdinaryLowTail_isLittleO_proved (hℓ : ℓ ≠ 0) (m : ℕ)
--       (hpnt : PrimaryPrimePNT) {C ξ : ℝ}
--       (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (hξ : 0 < ξ) (hξsmall : ξ < 1/100) :
--       ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ),
--         (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
--         (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
--         (∀ᶠ X : ℝ in atTop, H X ≤ X) →
--         (fun X => angular_scaleFirstOrdinaryLowTail ℓ m ξ (H X) (T X) X)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaOrdinaryTail.lean (declaration OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved)

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

theorem angular_scaleFirstOrdinaryLowTail_isLittleO_proved (hℓ : ℓ ≠ 0) (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξsmall : ξ < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => angular_scaleFirstOrdinaryLowTail ℓ m ξ (H X) (T X) X)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
