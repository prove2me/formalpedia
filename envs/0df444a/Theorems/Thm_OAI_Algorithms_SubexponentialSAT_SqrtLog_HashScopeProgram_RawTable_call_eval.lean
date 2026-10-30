-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_RawTable_call_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:28:45.245988+00:00
-- url     : https://prove2.me/theorems/cdc00776-f539-4971-b768-be0d26cd0757
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramRawCall.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramRawCall.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)`):
--
--   ```lean
--   theorem call_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
--       (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
--       (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
--       (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
--       (width modulus shape source out : List Bool) (hw : width.length=b)
--       (hm : BinaryArithmetic.toNat modulus=clauses.length)
--       (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
--       ∃ n ≤ FromTuple.cost t d b modulus clauses codes terms, ∃ rf,
--         Eval call n
--           (data zeroRegs (rowBits b terms).reverse width modulus
--             (Encoding.encodeList id clauses) shape [] source [] out [])
--           (data rf [] width modulus (Encoding.encodeList id clauses) shape
--             (scopeBytes (clauses := clauses) t d codes terms) source [] out [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.zeroRegs` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.rowBits` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.data` (definitions bundle `OAIQ081S085` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.scopeBytes` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramRawCall.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval)

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

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem call_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape source out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ FromTuple.cost t d b modulus clauses codes terms, ∃ rf,
      Eval call n
        (data zeroRegs (rowBits b terms).reverse width modulus
          (Encoding.encodeList id clauses) shape [] source [] out [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (scopeBytes (clauses := clauses) t d codes terms) source [] out []) := by
  sorry

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end
