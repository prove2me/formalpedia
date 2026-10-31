-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost_pair_cost_le_assembled
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:24:03.826887+00:00
-- url     : https://prove2.me/theorems/192a8964-f3f1-4934-a0f6-604c433370c0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryMeasuredCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryMeasuredCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost`, with `open OAI SqrtLog SubexpLiftRing SubexpQuarticRing`, `open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS`, `open CostAssembly.Polynomial`, `open scoped BigOperators`):
--
--   ```lean
--   theorem pair_cost_le_assembled (s : ProducedSource) {d : ℕ}
--       (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
--       (k N n A height : ℕ) (p : CostAssembly.Resources)
--       (hN : N ≤ s.input.n) (hsn : s.input.n ≤ n) (hs : s.bound ≤ A)
--       (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
--       (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power)
--       (horder : q.J = CostAssembly.jetOrder k n p)
--       (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
--       (hK : SignatureTupleRun.tupleCount s.key s.input.r ≤ p.labelBase^p.labelRows)
--       (hheight : height ≤ p.headSize) :
--       DifferencePairsProgram.cost
--         (QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
--           (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
--           (QueryHeadBudgets.transient A) height) N q.J ≤
--         pairCoefficient A*CostAssembly.assembledWork k n p^2+10
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.cost` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.source` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.jetOrder` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.tupleCount` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.transient` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pairCoefficient` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.power` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackBudget` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryMeasuredCost.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S191

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

theorem pair_cost_le_assembled (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (k N n A height : ℕ) (p : CostAssembly.Resources)
    (hN : N ≤ s.input.n) (hsn : s.input.n ≤ n) (hs : s.bound ≤ A)
    (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power)
    (horder : q.J = CostAssembly.jetOrder k n p)
    (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hK : SignatureTupleRun.tupleCount s.key s.input.r ≤ p.labelBase^p.labelRows)
    (hheight : height ≤ p.headSize) :
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height) N q.J ≤
      pairCoefficient A*CostAssembly.assembledWork k n p^2+10 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end
