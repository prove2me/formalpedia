-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_baseline_pass
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:18:55.906754+00:00
-- url     : https://prove2.me/theorems/8354980b-b9ee-4937-8fcd-649f7ce2f589
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SubexpSetupStorage LeafHeadSetupProgram`, `open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`, `open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource`):
--
--   ```lean
--   theorem baseline_pass {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
--       {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
--       {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (s : ProducedSource) (base : ℕ) (words : List (List Bool))
--       (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
--       (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
--       (hs : SignatureHeadLoader.MasterFrame s.masters
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hreps : a.stacks 837=suspendedFrames words)
--       (haddress : a.stacks 845=unary (base+words.length))
--       (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
--       (hbase : (a.stacks 869).length=s.input.n)
--       (hshape : ∀ pre word rest,words=pre++word::rest →
--         word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+rest.length)).length)
--       (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
--         s.input.columnLength s.bound ≤ B) :
--       ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.baselineHead) steps a b ∧
--         QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
--         DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
--         FrameCursor base [] b ∧ b.stacks 841=[] ∧
--         b.stacks 869=QueryRepresentativeFold.run (mask s) base words (a.stacks 869) ∧
--         (b.stacks 869).length=s.input.n ∧
--         (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
--         (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
--         steps+1 ≤ 18*B+8*(words.map List.length).sum+(baselineCost s B+10)*words.length+19 ∧
--         QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead)
--           (steps+1) a (max (896*B+baselineCost s B) (914*B+18))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.retainedOutputBound` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.suspendedFrames` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold.run` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.FrameCursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baselineCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.masters` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.mask` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.baselineHead` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass)

import Mathlib
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

theorem baseline_pass {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (s : ProducedSource) (base : ℕ) (words : List (List Bool))
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=unary (base+words.length))
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hbase : (a.stacks 869).length=s.input.n)
    (hshape : ∀ pre word rest,words=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+rest.length)).length)
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.baselineHead) steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      FrameCursor base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=QueryRepresentativeFold.run (mask s) base words (a.stacks 869) ∧
      (b.stacks 869).length=s.input.n ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(baselineCost s B+10)*words.length+19 ∧
      QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead)
        (steps+1) a (max (896*B+baselineCost s B) (914*B+18)) := by
  sorry

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end
