-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_arityCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:04:24.184991+00:00
-- url     : https://prove2.me/theorems/abfdcb26-2df7-421a-9d6f-aa2189c51171
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem arityCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
--       (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length)
--       (hp : projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
--         (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0)
--         false true false (LeafStatisticsProgram.scopeBits rows) []) :
--       ∃ n ≤ 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
--           (rows.map (Encoding.encodeList Encoding.encodeNat)), ∃ rf,
--         Eval arityCall n a (embedState r10 arity a
--           (LeafStatisticsProgram.Arity.state rf forward [] [] []
--             (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.budget` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.arity` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arity` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.r10` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.ports` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.state` (definitions bundle `OAIQ081S095` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall` (definitions bundle `OAIQ081S146` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S146

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem arityCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length)
    (hp : projectState r10 arity a = RecordPrograms.state LeafStatisticsProgram.Arity.ports
      (LeafStatisticsProgram.Arity.state (a.regs ∘ r10) forward [] [] [] 0 0)
      false true false (LeafStatisticsProgram.scopeBits rows) []) :
    ∃ n ≤ 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
        (rows.map (Encoding.encodeList Encoding.encodeNat)), ∃ rf,
      Eval arityCall n a (embedState r10 arity a
        (LeafStatisticsProgram.Arity.state rf forward [] [] []
          (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length)) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
