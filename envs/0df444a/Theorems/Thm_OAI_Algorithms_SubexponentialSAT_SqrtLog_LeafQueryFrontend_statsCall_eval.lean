-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_statsCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:34:46.586207+00:00
-- url     : https://prove2.me/theorems/d7ad4a2d-7ea5-4bac-84de-a79398e1bd55
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem statsCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
--       (hp : projectState r10 stats a = LeafStatisticsProgram.initial (a.regs ∘ r10) rows forward) :
--       ∃ n ≤ LeafStatisticsProgram.bootBudget rows forward+
--           LeafStatisticsProgram.variableBudget rows 0 forward+2, ∃ rf,
--         Eval statsCall n a (embedState r10 stats a
--           (LeafStatisticsProgram.variableState rf rows forward.length [] forward
--             (LeafStatisticsProgram.variableTotals rows 0 forward LeafStatisticsProgram.zeroTotals)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableTotals` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.r10` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.stats` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.zeroTotals` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableBudget` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.bootBudget` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableState` (definitions bundle `OAIQ081S130` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendCalls.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval)

import Mathlib
import Definitions.Def_OAIQ081S130

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem statsCall_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hp : projectState r10 stats a = LeafStatisticsProgram.initial (a.regs ∘ r10) rows forward) :
    ∃ n ≤ LeafStatisticsProgram.bootBudget rows forward+
        LeafStatisticsProgram.variableBudget rows 0 forward+2, ∃ rf,
      Eval statsCall n a (embedState r10 stats a
        (LeafStatisticsProgram.variableState rf rows forward.length [] forward
          (LeafStatisticsProgram.variableTotals rows 0 forward LeafStatisticsProgram.zeroTotals))) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
