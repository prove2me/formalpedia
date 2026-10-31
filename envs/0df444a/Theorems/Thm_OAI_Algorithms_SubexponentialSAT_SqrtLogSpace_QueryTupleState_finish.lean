-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleState_finish
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:39:44.707893+00:00
-- url     : https://prove2.me/theorems/0f77da83-4fae-4ac0-8703-8ef4c5b16e56
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleState.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleState.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing`, `open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes`, `open TruncatedRingProgram SubexpSetupStorage`):
--
--   ```lean
--   theorem finish {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
--       {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
--       {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
--       (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
--       (source : List (Product.Entry n (baseWidth 3 q.p.t) d))
--       (hsource : Good ∅ q.p.t q.J source) (hbytes : a.stacks 852=Product.bytes source)
--       (ha : WordBound B a)
--       (hcap : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
--       ∃ steps b, Eval QueryExecution.TupleEnd.command steps a b ∧
--         QueryReady q node H high E U P b ∧
--         PairAccumulatorMeaning q (value+Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)) b ∧
--         WordBound B b ∧ QueryMasterFrame a b ∧
--         (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
--         (∀ i,128≤ i.val → i∉SignatureTupleProgram.currentHeadPorts → i≠851 → i≠852 →
--           b.stacks i=a.stacks i) ∧
--         (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
--         steps+1≤QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+16*B+25
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instAdd` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.currentHeadPorts` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum.budget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.readout` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.rawValue` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryTupleState.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish)

import Mathlib
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

theorem finish {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (source : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hsource : Good ∅ q.p.t q.J source) (hbytes : a.stacks 852=Product.bytes source)
    (ha : WordBound B a)
    (hcap : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval QueryExecution.TupleEnd.command steps a b ∧
      QueryReady q node H high E U P b ∧
      PairAccumulatorMeaning q (value+Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)) b ∧
      WordBound B b ∧ QueryMasterFrame a b ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      (∀ i,128≤ i.val → i∉SignatureTupleProgram.currentHeadPorts → i≠851 → i≠852 →
        b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      steps+1≤QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+16*B+25 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end
