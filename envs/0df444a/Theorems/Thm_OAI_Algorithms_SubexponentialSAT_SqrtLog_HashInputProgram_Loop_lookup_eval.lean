-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_lookup_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:00:05.942825+00:00
-- url     : https://prove2.me/theorems/325940a5-846c-47e3-90b0-8d40cf66ae85
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoopTerm.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoopTerm.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives`):
--
--   ```lean
--   theorem lookup_eval (regs : Fin 8 → Bool) (clauses : List (List Bool))
--       (i : Fin clauses.length) (rest width modulus shape acc quotient : List Bool) :
--       ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf,
--         Eval lookup n
--           (data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
--             (Encoding.encodeNat i.val) [] [])
--           (data rf rest width modulus (Encoding.encodeList id clauses) shape acc quotient
--             [] clauses[i.val] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoopTerm.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem lookup_eval (regs : Fin 8 → Bool) (clauses : List (List Bool))
    (i : Fin clauses.length) (rest width modulus shape acc quotient : List Bool) :
    ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf,
      Eval lookup n
        (data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          (Encoding.encodeNat i.val) [] [])
        (data rf rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          [] clauses[i.val] []) := by
  sorry

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end
