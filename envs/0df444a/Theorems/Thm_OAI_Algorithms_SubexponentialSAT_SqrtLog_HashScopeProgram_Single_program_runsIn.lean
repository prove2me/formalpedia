-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Single_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:07:53.556738+00:00
-- url     : https://prove2.me/theorems/2f374859-cfc7-4871-bccd-ab7de77b0c3f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramSingle.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramSingle.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpChunkRecordMap (Data data tapes regs)`, `open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)`):
--
--   ```lean
--   theorem program_runsIn (terms : List Term) :
--       ∃ rf, RunsIn program (cost terms)
--         ((data false false false [] (Encoding.encodeList payload terms) [] []).withPC (some program.entry))
--         ((⟨rf,tapes [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩ : Data).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Term` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpChunkRecordMap.tapes` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.scope` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.cost` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpChunkRecordMap.data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashScopeProgramSingle.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S102

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpChunkRecordMap (Data data tapes regs)
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem program_runsIn (terms : List Term) :
    ∃ rf, RunsIn program (cost terms)
      ((data false false false [] (Encoding.encodeList payload terms) [] []).withPC (some program.entry))
      ((⟨rf,tapes [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩ : Data).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
end
