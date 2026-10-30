-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_fetchLiteral_from_state
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:50.080817+00:00
-- url     : https://prove2.me/theorems/05c8213b-6e6d-471c-a77f-c4b9f98c96f1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramLiteralState.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramLiteralState.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem fetchLiteral_from_state (d : Machine) (regs : Fin 5 → Bool) (old positive : Bool)
--       (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
--       (hlookup : entries.lookup (Encoding.encodeNat v) = some payload)
--       (hports : projectState literalRegisters literalStacks d =
--         data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
--           (Squarefree.Program.lookupRecords entries)) :
--       ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+10,
--         ∃ regs', Eval fetchLiteral n d
--           (literalFrame d regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
--           regs' 4 = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalRegisters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalStacks` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalFetchBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Machine` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalFrame` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramLiteralState.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem fetchLiteral_from_state (d : Machine) (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload)
    (hports : projectState literalRegisters literalStacks d =
      data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
        (Squarefree.Program.lookupRecords entries)) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+10,
      ∃ regs', Eval fetchLiteral n d
        (literalFrame d regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
        regs' 4 = true := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end
