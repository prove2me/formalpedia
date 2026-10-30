-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Marked_fetch_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:07:47.306125+00:00
-- url     : https://prove2.me/theorems/823289fc-9506-4283-aac2-b21e86ae693f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramMarkedSource.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramMarkedSource.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )`):
--
--   ```lean
--   theorem fetch_eval (clauses : List (List Bool)) (i : Fin clauses.length) (rf : Fin 11 → Bool)
--       (width modulus shape out : List Bool) :
--       ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf',
--         Eval fetch n
--           (data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] [])
--           (data rf' width modulus (Encoding.encodeList id clauses) shape out [] [] clauses[i.val] [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch` (definitions bundle `OAIQ081S085` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.data` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramMarkedSource.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

theorem fetch_eval (clauses : List (List Bool)) (i : Fin clauses.length) (rf : Fin 11 → Bool)
    (width modulus shape out : List Bool) :
    ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf',
      Eval fetch n
        (data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape out [] [] clauses[i.val] [] []) := by
  sorry

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end
