-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_primeProductGaussTail_angular_isLittleO_proved
-- name    : OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:46.295893+00:00
-- url     : https://prove2.me/theorems/5786dae5-e108-4548-8e86-a4978fc6b581
-- title:
--   OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaGaussTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaGaussTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Asymptotics`, `open scoped BigOperators`):
--
--   ```lean
--   theorem primeProductGaussTail_angular_isLittleO_proved
--       (hℓ : ℓ ≠ 0)
--       (hpnt : PrimaryPrimePNT) (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       :
--       ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
--         (fun X => primeProductGaussTail ℓ (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primeProductGaussTail` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_isLittleO` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaGaussTail.lean (declaration OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

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

theorem primeProductGaussTail_angular_isLittleO_proved
    (hℓ : ℓ ≠ 0)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    :
    ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
      (fun X => primeProductGaussTail ℓ (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
