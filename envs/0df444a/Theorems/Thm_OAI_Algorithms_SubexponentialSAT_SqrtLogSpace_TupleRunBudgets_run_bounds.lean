-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TupleRunBudgets_run_bounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:24:29.364114+00:00
-- url     : https://prove2.me/theorems/8f7ca2bc-799d-475f-979a-6910ba03d03b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TupleRunBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TupleRunBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets`, with `open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial`, `open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader`):
--
--   ```lean
--   theorem run_bounds (s : ProducedSource) {d : ℕ}
--       (q : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
--       (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
--       (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
--       (hp : q.p.power = s.input.power) :
--       SignatureTupleRun.completeSpace s q (QueryHeadBudgets.compact A)
--         (QueryHeadBudgets.transient A) ≤ runCoefficient A ∧
--       ∀ height, SignatureTupleRun.runTime s q (QueryHeadBudgets.compact A)
--         (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
--         (QueryHeadBudgets.transient A) height ≤
--         runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.source` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.tupleCount` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.transient` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.runCoefficient` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.power` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.completeSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.runTime` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TupleRunBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds)

import Mathlib
import Definitions.Def_OAIQ081S191

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

theorem run_bounds (s : ProducedSource) {d : ℕ}
    (q : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    SignatureTupleRun.completeSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ runCoefficient A ∧
    ∀ height, SignatureTupleRun.runTime s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end
