-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_TypeCompare_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:10.550627+00:00
-- url     : https://prove2.me/theorems/36473254-82cd-4220-ae4f-51c140fd8a46
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramTypeCompare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramTypeCompare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem command_eval (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
--       (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
--       ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+34,
--         ∃ e : Data, Eval command n a e ∧ e.stacks=a.stacks ∧
--           e.regs 7=decide (a.stacks 23=a.stacks 24)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.Data` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramTypeCompare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S091

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem command_eval (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
    ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+34,
      ∃ e : Data, Eval command n a e ∧ e.stacks=a.stacks ∧
        e.regs 7=decide (a.stacks 23=a.stacks 24) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
end
