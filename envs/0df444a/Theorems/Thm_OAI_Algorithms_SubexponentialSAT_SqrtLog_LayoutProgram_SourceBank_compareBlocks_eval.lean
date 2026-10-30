-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_compareBlocks_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:43:24.224538+00:00
-- url     : https://prove2.me/theorems/bf8cfa53-43e8-4285-bdb6-3f2bc1517241
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameCalls.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameCalls.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem compareBlocks_eval (a : Data) (h301 : a.stacks 301=[]) (h302 : a.stacks 302=[])
--       (h303 : a.stacks 303=[]) (h307 : a.stacks 307=[]) :
--       ∃ n ≤ 18*(a.stacks 288).length+9*(a.stacks 291).length+32,
--         ∃ e : Data, Eval compareBlocks n a e ∧ e.stacks=a.stacks ∧
--           e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 288=a.stacks 291)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks` (definitions bundle `OAIQ081S168` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameCalls.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval)

import Mathlib
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem compareBlocks_eval (a : Data) (h301 : a.stacks 301=[]) (h302 : a.stacks 302=[])
    (h303 : a.stacks 303=[]) (h307 : a.stacks 307=[]) :
    ∃ n ≤ 18*(a.stacks 288).length+9*(a.stacks 291).length+32,
      ∃ e : Data, Eval compareBlocks n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 288=a.stacks 291) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end
