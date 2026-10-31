-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_primeProductGaussTail_radial_isLittleO
-- name    : OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:25:55.628994+00:00
-- url     : https://prove2.me/theorems/bb84439c-89ef-4625-84a8-0ff902e48ebc
-- title:
--   OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialGaussTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialGaussTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Asymptotics`, `open scoped BigOperators`):
--
--   ```lean
--   theorem cubicTheta_primeProductGaussTail_radial_isLittleO
--       (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       :
--       ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
--         (fun X => primeProductGaussTail 0 (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
--           =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primeProductGaussTail` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_isLittleO` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialGaussTail.lean (declaration OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO)

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

theorem cubicTheta_primeProductGaussTail_radial_isLittleO
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    :
    ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
      (fun X => primeProductGaussTail 0 (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
