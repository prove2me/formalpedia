-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_loop_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:28:13.433404+00:00
-- url     : https://prove2.me/theorems/f0059b14-111f-4b41-b593-fd2161d09796
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem loop_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
--       (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
--       (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
--       (width modulus shape acc : List Bool)
--       (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
--       (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
--       ∃ n ≤ loopBudget t d b modulus.length clauses terms, ∃ rf,
--         Eval loop n
--           (data regs (scanInput b terms) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
--           (data rf [] width modulus (Encoding.encodeList id clauses) shape
--             (records (terms.reverse.map (payload t d clauses)) acc) [] [] [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.records` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.scanInput` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loopBudget` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.payload` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramLoop.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem loop_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape acc : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ loopBudget t d b modulus.length clauses terms, ∃ rf,
      Eval loop n
        (data regs (scanInput b terms) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (records (terms.reverse.map (payload t d clauses)) acc) [] [] [] []) := by
  sorry

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end
