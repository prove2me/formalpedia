-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_Program_eraseOne_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:13:08.932494+00:00
-- url     : https://prove2.me/theorems/f8112a8f-2f98-4ad6-9631-ab7977de9947
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeProgramErase.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeProgramErase.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan`):
--
--   ```lean
--   theorem eraseOne_eval (regs : Fin 5 → Bool) (key query payload tail output : List Bool) :
--       ∃ n ≤ 28 * key.length + 9 * query.length + 13 * payload.length + 50, ∃ final,
--         Eval eraseOne n
--           (eraseData regs (Encoding.frame key ++ Encoding.frame payload ++ tail) query output [])
--           (eraseData final tail query
--             (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseData` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeProgramErase.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem eraseOne_eval (regs : Fin 5 → Bool) (key query payload tail output : List Bool) :
    ∃ n ≤ 28 * key.length + 9 * query.length + 13 * payload.length + 50, ∃ final,
      Eval eraseOne n
        (eraseData regs (Encoding.frame key ++ Encoding.frame payload ++ tail) query output [])
        (eraseData final tail query
          (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) []) := by
  sorry
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end
