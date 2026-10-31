-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_kummerPrimeSiegelWalfisz_of_primitive
-- name    : OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:00:57.236657+00:00
-- url     : https://prove2.me/theorems/5f4e3e19-b460-460a-a778-0f51beea5ab7
-- title:
--   OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive` of [lean/OAI/NumberTheory/CubicMoment/Estimates/KummerPrimeFromPrimitive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/KummerPrimeFromPrimitive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`):
--
--   ```lean
--   theorem kummerPrimeSiegelWalfisz_of_primitive (hpub : PrimitiveResidueHeckeInput) :
--       KummerPrimeSiegelWalfisz
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.KummerPrimeSiegelWalfisz` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/KummerPrimeFromPrimitive.lean (declaration OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive)

import Mathlib
import Definitions.Def_OAIQ096A007

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace CubicFirstMoment

theorem kummerPrimeSiegelWalfisz_of_primitive (hpub : PrimitiveResidueHeckeInput) :
    KummerPrimeSiegelWalfisz := by
  sorry

end CubicFirstMoment

end

end OAI
end
