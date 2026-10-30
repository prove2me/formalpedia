-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_RowSelectionProgram_multiplyReuseCommand_eval_total
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:31.675463+00:00
-- url     : https://prove2.me/theorems/fe89dda8-1a56-4e70-a347-323fd80b7cd7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramTotal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramTotal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ArithmeticCalls`):
--
--   ```lean
--   theorem multiplyReuseCommand_eval_total (d : Data) (hd : Ready d) :
--       ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
--         Eval multiplyReuseCommand t d (pairState regs positive negative) ∧
--         signedValue positive negative =
--           signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) ∧
--         pairTotal positive negative =
--           pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
--         positive.length + negative.length ≤ 2*inputLength d+6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairTotal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.signedValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Data` (definitions bundle `OAIQ081S033` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.inputLength` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairState` (definitions bundle `OAIQ081S080` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/RowSelectionProgramTotal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total)

import Mathlib
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S080

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ArithmeticCalls

theorem multiplyReuseCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval multiplyReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal positive negative =
        pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ 2*inputLength d+6 := by
  sorry

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end
