-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumCorrect_prepared_head_update
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:34:50.990926+00:00
-- url     : https://prove2.me/theorems/00d53910-3381-4177-b624-c861aea52c74
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram`, `open scoped BigOperators`, `open HeadIdentifierProgram`):
--
--   ```lean
--   theorem prepared_head_update {n r : ℕ} (H : Finset (Fin n))
--       (high : H → Bool) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
--       (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ _ : v ∉ H, head v = g)
--       (reps : ∀ k, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) k → Bool)
--       (candidate : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
--       {steps : ℕ} (a b : HeadSumProgram.Data)
--       (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
--       (hbits : a.stacks 859 = List.ofFn
--         (BucketTupleProgram.Concrete.freeAssignmentEquiv H
--           (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
--           (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
--       (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
--       (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
--         (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps))) :
--       b.stacks 145 =
--         List.ofFn (HighIncidence.glue H high
--           (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val)
--             (Function.update reps g candidate)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete.freeAssignmentEquiv` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_nodup` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.assemble` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.prepare` (definitions bundle `OAIQ081S162` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update)

import Mathlib
import Definitions.Def_OAIQ081S162

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators

open HeadIdentifierProgram

theorem prepared_head_update {n r : ℕ} (H : Finset (Fin n))
    (high : H → Bool) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ _ : v ∉ H, head v = g)
    (reps : ∀ k, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) k → Bool)
    (candidate : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
    {steps : ℕ} (a b : HeadSumProgram.Data)
    (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
    (hbits : a.stacks 859 = List.ofFn
      (BucketTupleProgram.Concrete.freeAssignmentEquiv H
        (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps))) :
    b.stacks 145 =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val)
          (Function.update reps g candidate))) := by
  sorry

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end
