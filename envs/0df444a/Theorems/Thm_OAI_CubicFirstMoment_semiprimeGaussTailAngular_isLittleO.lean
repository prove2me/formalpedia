-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_semiprimeGaussTailAngular_isLittleO
-- name    : OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:14.15004+00:00
-- url     : https://prove2.me/theorems/5bdc0d4f-b6bc-4cd4-af9c-12fc60b98bec
-- title:
--   OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailAngularFull.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailAngularFull.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem semiprimeGaussTailAngular_isLittleO
--       (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
--       ∃ m : ℕ, ∀ Ct : ℕ, m ≤ Ct → ∀ H : ℝ → ℝ,
--         (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+1/3000:ℝ)) →
--         (fun X => semiprimeGaussTailAngular ℓ (H X) ((1+Real.log X)^Ct) X)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.semiprimeGaussTailAngular` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SemiprimeGaussTailAngularFull.lean (declaration OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

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
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem semiprimeGaussTailAngular_isLittleO
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ m : ℕ, ∀ Ct : ℕ, m ≤ Ct → ∀ H : ℝ → ℝ,
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X ∧ H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => semiprimeGaussTailAngular ℓ (H X) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
