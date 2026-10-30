-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafNodeCacheProgram_local_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:10:28.213893+00:00
-- url     : https://prove2.me/theorems/2d0d9f10-172d-4b93-b15e-ba8f8b4b4c50
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafNodeCacheProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafNodeCacheProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage`):
--
--   ```lean
--   theorem local_eval (a : LocalData) (h : Ready a.stacks) :
--       ∃ rr, Eval localCommand (localBudget a) a
--         (finalState (prepared a) rr (rawOne a.stacks))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.Ready` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.rawOne` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.LocalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.localCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.prepared` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.finalState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.localBudget` (definitions bundle `OAIQ081S108` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafNodeCacheProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval)

import Mathlib
import Definitions.Def_OAIQ081S108

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem local_eval (a : LocalData) (h : Ready a.stacks) :
    ∃ rr, Eval localCommand (localBudget a) a
      (finalState (prepared a) rr (rawOne a.stacks)) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end
