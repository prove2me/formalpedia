-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_positive_run_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:37:02.375254+00:00
-- url     : https://prove2.me/theorems/d2e0a470-113e-4f07-b7d6-84bf9df66bea
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun`, with `open Classical`, `open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram`, `open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource`, `open SignatureTupleComplete`):
--
--   ```lean
--   theorem positive_run_resources (s : ProducedSource) {d M F S Z B width height : ℕ}
--       (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
--       (H E U : Finset (Fin s.input.n)) (high : H → Bool)
--       (owner : Fin q.ps.length → Fin s.input.n)
--       (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
--       (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
--       (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
--       (cap : RetainedCap s F) (hpositive : 0 < s.input.r)
--       (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
--       (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
--       (hbound : WordBound F a)
--       (hm : SignatureHeadLoader.MasterFrame s.masters
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hz : a.stacks 649=unary s.base)
--       (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
--       (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
--       ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
--         BitProgram.Trace SignatureTupleComplete.program (steps+1)
--           (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
--         QueryTupleState.QueryReady q s.input.node H high E U M b ∧
--         QueryTupleState.PairAccumulatorMeaning q
--           (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
--         WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
--         steps+1 ≤ eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*
--           tupleCount s.key s.input.r*4^height+tupleCount s.key s.input.r*leafCost s q F S Z B height+2 ∧
--         ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
--           (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
--           ∀ i,(cfg.stacks i).length ≤ runSpace s q F B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instAdd` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.tupleCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.tupleTotal` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.eventPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.runSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.masters` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.emittedValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.leafCost` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.program` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources)

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
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

theorem positive_run_resources (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0 < s.input.r)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q s.input.node H high E U M b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
      steps+1 ≤ eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*
        tupleCount s.key s.input.r*4^height+tupleCount s.key s.input.r*leafCost s q F S Z B height+2 ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
        (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ runSpace s q F B := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end
