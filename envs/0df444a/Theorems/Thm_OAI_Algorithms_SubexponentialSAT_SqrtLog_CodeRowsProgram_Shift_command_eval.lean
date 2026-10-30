-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_Shift_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:07.412739+00:00
-- url     : https://prove2.me/theorems/9dc5af17-9ec5-4eff-bf1e-560c43812510
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramShift.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramShift.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem command_eval (pairs : List (Bool × Bool)) (side : Bool)
--       (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
--       ∃ rf, rf 7=side ∧ Eval command (14*pairs.length+5)
--         (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) [] [])
--         (state rf tail [] [] (result side pairs))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.result` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.frames` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.state` (definitions bundle `OAIQ081S084` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramShift.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S084

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
    ∃ rf, rf 7=side ∧ Eval command (14*pairs.length+5)
      (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) [] [])
      (state rf tail [] [] (result side pairs)) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end
