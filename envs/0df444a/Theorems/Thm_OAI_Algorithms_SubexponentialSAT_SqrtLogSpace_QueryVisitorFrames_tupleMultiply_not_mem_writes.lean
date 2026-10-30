-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorFrames_tupleMultiply_not_mem_writes
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:20:32.923224+00:00
-- url     : https://prove2.me/theorems/9b798e92-a0d8-4b52-a432-a4f190402ff9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorFrames.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorFrames.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames`, with `open OAI BitProgram StructuredCalls`, `open CommandRegisterFrames QueryTupleVisitor`):
--
--   ```lean
--   theorem tupleMultiply_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
--       i ∉ writes QueryAssembler.TupleMultiply.command
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames.writes` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.TupleMultiply.command` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorFrames.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes)

import Mathlib
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

open OAI BitProgram StructuredCalls
open CommandRegisterFrames QueryTupleVisitor

theorem tupleMultiply_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.TupleMultiply.command := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames
end
