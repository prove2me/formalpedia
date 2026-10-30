-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryExecution_TupleEnd_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:16:26.268799+00:00
-- url     : https://prove2.me/theorems/81acb131-4133-4df1-b739-56eb6446d30c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd`, with `open OAI BitProgram StructuredCalls`, `open QueryTupleVisitor SignatureTupleProgram`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`):
--
--   ```lean
--   theorem command_run (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
--       (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
--       (width degree : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
--       (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
--       (hr : QueryTupleSum.Ready a M.bits width degree (Product.bytes seed) (Product.bytes source))
--       (hcap : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2) ≤ B) :
--       let output := Normalize.run p t M cache source seed
--       ∃ steps rr, Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
--         Good ∅ u J output ∧
--         (∀ i, ((result a rr M.bits width degree (Product.bytes output)).stacks i).length ≤ B) ∧
--         steps+1 ≤ QueryTupleSum.budget n (baseWidth p t) d u J B+16*B+25
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum.budget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum.Ready` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.result` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run)

import Mathlib
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

namespace TupleEnd

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram

theorem command_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hr : QueryTupleSum.Ready a M.bits width degree (Product.bytes seed) (Product.bytes source))
    (hcap : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2) ≤ B) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
      Good ∅ u J output ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes output)).stacks i).length ≤ B) ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth p t) d u J B+16*B+25 := by
  sorry

end TupleEnd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end
