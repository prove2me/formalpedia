-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceExpression_literal_length_le_sourceLengthBound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:31:09.213885+00:00
-- url     : https://prove2.me/theorems/987d225e-b2d3-46ef-9701-33185ac7b3fa
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpressionBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpressionBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression`, with `open SubexponentialSAT.Subexp UniversalRowSourceBound PolynomialExecutorProgram`):
--
--   ```lean
--   theorem literal_length_le_sourceLengthBound {B d S : ℕ}
--       (c : Coeff B d) (hwidth : d * B ≤ S) :
--       (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ sourceLengthBound S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.pushWord` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` (definitions bundle `OAIQ081S125` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpressionBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound)

import Mathlib
import Definitions.Def_OAIQ081S125

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT.Subexp UniversalRowSourceBound PolynomialExecutorProgram

theorem literal_length_le_sourceLengthBound {B d S : ℕ}
    (c : Coeff B d) (hwidth : d * B ≤ S) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ sourceLengthBound S := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
end
