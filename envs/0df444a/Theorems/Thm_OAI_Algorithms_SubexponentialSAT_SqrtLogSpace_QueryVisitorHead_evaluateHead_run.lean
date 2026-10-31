-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorHead_evaluateHead_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:36:15.794637+00:00
-- url     : https://prove2.me/theorems/0837b157-b0e1-4fa2-9785-b4c3578e0f60
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram`, `open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage`, `open scoped BigOperators`):
--
--   ```lean
--   theorem evaluateHead_run (s : LeafHeadSetupProgram.Native.Inputs) {d M P S Z B L width B₀ : ℕ}
--       (q : Factor.Spec s.r s.Q s.n d) (H E U : Finset (Fin s.n)) (high : H → Bool)
--       (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
--       (head : Fin s.Q → Fin s.n → Fin s.r) (facts : SourceFacts s q H owner nativeOwner head)
--       (caps : HeadBounds s q M P S Z B L width) (g : Fin s.r)
--       (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.node v.val) k → Bool)
--       (source : LeafHeadSetupProgram.Data) (hsource : LeafHeadSetupProgram.Native.Ready s source)
--       (hsourceBound : WordBound B₀ source)
--       (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
--       (hwords : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
--       (a : State 40 896)
--       (hmaster : SignatureHeadLoader.MasterFrame (LeafHeadSetupProgram.Native.start s source ra rd rc words)
--         (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
--       (hq : QueryReady q s.node H high E U M a) (ha : WordBound P a)
--       {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (hpair : PairAccumulatorMeaning q pairValue a) (htuple : DenseWord q 852 tupleValue a)
--       (hbase : a.stacks 869=List.ofFn (HighIncidence.glue H high
--         (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.node v.val) reps)))
--       (hbits : a.stacks 838=representativeWord s q H owner nativeOwner head facts g reps)
--       (haddress : a.stacks 843=LeafHeadSetupProgram.unary (s.node.val*s.r+g.val))
--       (hW : (a.stacks 141).length ≤ L) :
--       ∃ steps b,Eval QueryVisitorProgram.evaluateHead steps a b ∧
--         QueryReady q s.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
--         DenseWord q 852 (tupleValue*headValue q s.node H E U high owner head g reps (factorIds s g)) b ∧
--         b.stacks 853=[] ∧ b.stacks 841=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
--         (∀ i∈visitorPorts,b.stacks i=a.stacks i) ∧
--         (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
--         steps ≤ QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
--           sumBudget q P S Z B (count (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n)+
--           multiplyBudget q P ∧
--         QueryExecution.PrefixBound QueryVisitorProgram.evaluateHead steps a
--           (max (QueryVisitorLoad.runEnvelope B₀ P)
--             (max (996*P+200) (max B (896*P+multiplyBudget q P))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.predicate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.visitorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.runEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.lowStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.assemble` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.factorIds` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.multiplyBudget` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.representativeWord` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.headValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.sumBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.evaluateHead` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` (definitions bundle `OAIQ081S193` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run)

import Mathlib
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

theorem evaluateHead_run (s : LeafHeadSetupProgram.Native.Inputs) {d M P S Z B L width B₀ : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H E U : Finset (Fin s.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) (facts : SourceFacts s q H owner nativeOwner head)
    (caps : HeadBounds s q M P S Z B L width) (g : Fin s.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.node v.val) k → Bool)
    (source : LeafHeadSetupProgram.Data) (hsource : LeafHeadSetupProgram.Native.Ready s source)
    (hsourceBound : WordBound B₀ source)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hwords : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (a : State 40 896)
    (hmaster : SignatureHeadLoader.MasterFrame (LeafHeadSetupProgram.Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hq : QueryReady q s.node H high E U M a) (ha : WordBound P a)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a) (htuple : DenseWord q 852 tupleValue a)
    (hbase : a.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.node v.val) reps)))
    (hbits : a.stacks 838=representativeWord s q H owner nativeOwner head facts g reps)
    (haddress : a.stacks 843=LeafHeadSetupProgram.unary (s.node.val*s.r+g.val))
    (hW : (a.stacks 141).length ≤ L) :
    ∃ steps b,Eval QueryVisitorProgram.evaluateHead steps a b ∧
      QueryReady q s.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q s.node H E U high owner head g reps (factorIds s g)) b ∧
      b.stacks 853=[] ∧ b.stacks 841=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈visitorPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
        sumBudget q P S Z B (count (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n)+
        multiplyBudget q P ∧
      QueryExecution.PrefixBound QueryVisitorProgram.evaluateHead steps a
        (max (QueryVisitorLoad.runEnvelope B₀ P)
          (max (996*P+200) (max B (896*P+multiplyBudget q P)))) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end
