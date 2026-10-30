-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaArithmeticAxisDerivative_re_neg
-- name    : OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:24:30.557986+00:00
-- url     : https://prove2.me/theorems/70a8b6ba-2efe-4a55-bb27-071aba95f1cd
-- title:
--   OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaBaseScalarValue.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaBaseScalarValue.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`):
--
--   ```lean
--   lemma cubicThetaArithmeticAxisDerivative_re_neg :
--       (cubicThetaArithmeticAxisDerivative 1).re<0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative` (definitions bundle `OAIQ096A012` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq` and `OAI_CubicFirstMoment_uniform_cubicTheta_centered_subpower` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaBaseScalarValue.lean (declaration OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg)

import Mathlib
import Definitions.Def_OAIQ096A012

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaArithmeticAxisDerivative_re_neg :
    (cubicThetaArithmeticAxisDerivative 1).re<0 := by
  sorry

end CubicFirstMoment

end

end OAI
end
