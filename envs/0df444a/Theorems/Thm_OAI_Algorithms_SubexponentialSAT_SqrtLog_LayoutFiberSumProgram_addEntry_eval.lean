-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_addEntry_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:08:14.050791+00:00
-- url     : https://prove2.me/theorems/b0713ec3-ccde-42b3-99f7-054cc239054d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramBasic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramBasic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open RowSelectionProgram`):
--
--   ```lean
--   theorem addEntry_eval (base : Data) (hb : ArithmeticReady base)
--       (regs : Fin 16 → Bool) (queue column : List Bool) (acc next : WordPair) :
--       ∃ n ≤ 25000*(pairLength acc+pairLength next+3)^2+2, ∃ rf result,
--         Eval addEntry n (data base regs queue column acc next)
--           (data base rf queue column result ([],[])) ∧
--         pairValue result=pairValue acc+pairValue next ∧
--         pairTotal result.1 result.2=pairTotal acc.1 acc.2+pairTotal next.1 next.2 ∧
--         pairLength result ≤ pairLength acc+pairLength next+2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairTotal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Data` (definitions bundle `OAIQ081S087` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.ArithmeticReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.data` (definitions bundle `OAIQ081S106` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgramBasic.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval)

import Mathlib
import Definitions.Def_OAIQ081S106

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

theorem addEntry_eval (base : Data) (hb : ArithmeticReady base)
    (regs : Fin 16 → Bool) (queue column : List Bool) (acc next : WordPair) :
    ∃ n ≤ 25000*(pairLength acc+pairLength next+3)^2+2, ∃ rf result,
      Eval addEntry n (data base regs queue column acc next)
        (data base rf queue column result ([],[])) ∧
      pairValue result=pairValue acc+pairValue next ∧
      pairTotal result.1 result.2=pairTotal acc.1 acc.2+pairTotal next.1 next.2 ∧
      pairLength result ≤ pairLength acc+pairLength next+2 := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end
