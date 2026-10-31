-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_tailHighOrdinaryArity_isLittleO
-- name    : OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:46:06.600761+00:00
-- url     : https://prove2.me/theorems/abea51a1-70eb-4249-9ff3-819bb2f85d87
-- title:
--   OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO` of [lean/OAI/NumberTheory/CubicMoment/Estimates/TailHighOrdinaryNegligible.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailHighOrdinaryNegligible.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tailHighOrdinaryArity_isLittleO (i : ℕ)
--       (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
--       ∃ Ct : ℕ, ∀ H T : ℝ → ℝ,
--         (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
--         (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
--         (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
--         (fun X => tailHighOrdinaryArity i ξ (H X) (T X) X) =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.tailHighOrdinaryArity` (definitions bundle `OAIQ096A020` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailHighOrdinaryNegligible.lean (declaration OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020

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

theorem tailHighOrdinaryArity_isLittleO (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ Ct : ℕ, ∀ H T : ℝ → ℝ,
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => tailHighOrdinaryArity i ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
