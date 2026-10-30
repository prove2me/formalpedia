-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram_multiply_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:39:36.23848+00:00
-- url     : https://prove2.me/theorems/4f961ce1-c837-4ace-b595-280fc7f39f22
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`, `open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage`):
--
--   ```lean
--   theorem multiply_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
--       {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
--       {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {left right : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
--       (hl : DenseWord q 852 left a) (hh : DenseWord q 853 right a)
--       (ha : WordBound B a)
--       (hcap : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J≤B) :
--       ∃ steps b, Eval QueryAssembler.TupleMultiply.command steps a b ∧
--         QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
--         DenseWord q 852 (left*right) b ∧ b.stacks 853=[] ∧ QueryMasterFrame a b ∧
--         WordBound B b ∧
--         (∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
--           b.stacks i=a.stacks i) ∧
--         (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
--         steps+1≤51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J ∧
--         QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command (steps+1) a
--           (896*B+51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.byteBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.pairScratch` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.budget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.TupleMultiply.command` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.Data` (definitions bundle `OAIQ081S179` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` (definitions bundle `OAIQ081S185` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorCorrect.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run)

import Mathlib
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

theorem multiply_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {left right : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hl : DenseWord q 852 left a) (hh : DenseWord q 853 right a)
    (ha : WordBound B a)
    (hcap : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J≤B) :
    ∃ steps b, Eval QueryAssembler.TupleMultiply.command steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (left*right) b ∧ b.stacks 853=[] ∧ QueryMasterFrame a b ∧
      WordBound B b ∧
      (∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
        b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      steps+1≤51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J ∧
      QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command (steps+1) a
        (896*B+51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end
