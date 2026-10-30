-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_readCoefficient_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:25:40.143955+00:00
-- url     : https://prove2.me/theorems/98daab5a-afce-46e3-b995-d382efe9fa29
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRead.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRead.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem readCoefficient_eval (d : Data) (a b : Bool) (tail : List Bool)
--       (hs : d.stacks 0=Cell.frame a b++tail) :
--       Eval readCoefficient 6 d
--         ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.frame` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficientRegs` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient` (definitions bundle `OAIQ081S118` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRead.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval)

import Mathlib
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem readCoefficient_eval (d : Data) (a b : Bool) (tail : List Bool)
    (hs : d.stacks 0=Cell.frame a b++tail) :
    Eval readCoefficient 6 d
      ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
