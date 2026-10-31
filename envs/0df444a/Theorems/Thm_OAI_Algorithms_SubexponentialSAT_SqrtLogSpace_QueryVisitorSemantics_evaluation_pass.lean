-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_evaluation_pass
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:36:24.854765+00:00
-- url     : https://prove2.me/theorems/9a7ad320-0377-458e-b33d-ef5be89b3620
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SubexpSetupStorage LeafHeadSetupProgram`, `open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram`, `open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource`, `open scoped BigOperators`):
--
--   ```lean
--   theorem evaluation_pass (s : ProducedSource) {d M P S Z B width height : ℕ}
--       (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
--       (H E U : Finset (Fin s.input.n)) (high : H → Bool)
--       (owner : Fin q.ps.length → Fin s.input.n)
--       (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
--       (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
--       (caps : QueryVisitorHead.HeadBounds s.input q M P S Z B s.bound width)
--       (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool)
--       (hbalanced : ∀ g : Fin s.input.r,
--         HeadIdentifierProgram.count (HeadIdentifierProgram.predicate s.input.rows s.input.low
--           (s.base+g.val)) s.input.n ≤ height)
--       (a : Data)
--       {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {initial : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (hr : QueryReady q s.input.node H high E U M a)
--       (hm : PairAccumulatorMeaning q pairValue a)
--       (hv : DenseWord q 852 initial a) (ha : WordBound P a)
--       (hs : SignatureHeadLoader.MasterFrame s.masters
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
--         QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse)
--       (haddress : a.stacks 845=unary (s.base+s.input.r))
--       (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
--       (hbaseline : a.stacks 869=List.ofFn (HighIncidence.glue H high
--         (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.input.node v.val) reps))) :
--       ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.evaluateHead) steps a b ∧
--         QueryReady q s.input.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
--         DenseWord q 852 (initial*∏ g : Fin s.input.r,
--           QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
--             (QueryVisitorHead.factorIds s.input g)) b ∧
--         QueryMasterFrame a b ∧ WordBound P b ∧ FrameCursor s.base [] b ∧ b.stacks 841=[] ∧
--         b.stacks 869=a.stacks 869 ∧
--         (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
--         (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
--         steps+1 ≤ 26*P+(evaluationCost s q P S Z B height+10)*s.input.r+19 ∧
--         QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.evaluateHead)
--           (steps+1) a (max (evaluationSpace s q P B) (914*P+18))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.predicate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.assemble` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.suspendedFrames` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.factorIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.FrameCursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluationSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.masters` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.representativeWord` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.headValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.evaluateHead` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluationCost` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass)

import Mathlib
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193

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

open scoped BigOperators

theorem evaluation_pass (s : ProducedSource) {d M P S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M P S Z B s.bound width)
    (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool)
    (hbalanced : ∀ g : Fin s.input.r,
      HeadIdentifierProgram.count (HeadIdentifierProgram.predicate s.input.rows s.input.low
        (s.base+g.val)) s.input.n ≤ height)
    (a : Data)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {initial : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q s.input.node H high E U M a)
    (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 initial a) (ha : WordBound P a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
      QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse)
    (haddress : a.stacks 845=unary (s.base+s.input.r))
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hbaseline : a.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.input.node v.val) reps))) :
    ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.evaluateHead) steps a b ∧
      QueryReady q s.input.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (initial*∏ g : Fin s.input.r,
        QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
          (QueryVisitorHead.factorIds s.input g)) b ∧
      QueryMasterFrame a b ∧ WordBound P b ∧ FrameCursor s.base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=a.stacks 869 ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps+1 ≤ 26*P+(evaluationCost s q P S Z B height+10)*s.input.r+19 ∧
      QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.evaluateHead)
        (steps+1) a (max (evaluationSpace s q P B) (914*P+18)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end
