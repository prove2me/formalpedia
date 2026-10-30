-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_literalDictionary_hit
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:59:26.89855+00:00
-- url     : https://prove2.me/theorems/206ffeb5-8b31-4b27-aa4a-c2783ab40ac3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramPayload.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramPayload.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan`):
--
--   ```lean
--   theorem literalDictionary_hit (regs : Fin 5 → Bool) (old positive : Bool)
--       (key payload : List Bool) (entries : List (List Bool × List Bool))
--       (hlookup : entries.lookup key = some payload) :
--       ∃ n ≤ literalFetchBudget key entries + 9*payload.length+9, ∃ regs',
--         Eval literalDictionary n
--           (data regs old [] (key ++ [positive]).reverse []
--             (Squarefree.Program.lookupRecords entries))
--           (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
--         regs' 4 = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalFetchBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.data` (definitions bundle `OAIQ081S084` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramPayload.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit)

import Mathlib
import Definitions.Def_OAIQ081S084

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem literalDictionary_hit (regs : Fin 5 → Bool) (old positive : Bool)
    (key payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup key = some payload) :
    ∃ n ≤ literalFetchBudget key entries + 9*payload.length+9, ∃ regs',
      Eval literalDictionary n
        (data regs old [] (key ++ [positive]).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end
