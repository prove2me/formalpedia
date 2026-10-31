-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEmittedSourceTarget_signed_target
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:10:11.202485+00:00
-- url     : https://prove2.me/theorems/bf022b21-b654-478a-9100-5b2f06b098f7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEmittedSourceTarget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEmittedSourceTarget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget`, with `open scoped BigOperators`, `open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafProgram NodeConcrete Moments`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleSource`, `open SignatureTupleRun HeadSourceLocality BucketTupleProgram.Concrete`):
--
--   ```lean
--   theorem signed_target (hu : q.u = q.p.t)
--       (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
--       (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
--       (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t s.input.Q q.p.ht q.p.hfield s.input.node)
--       (ids : List ℕ) (hn : ids.Nodup)
--       (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
--       (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
--       (color : ℕ → Fin s.input.r)
--       (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g))
--       (hslot : ∀ f ∈ ids, ∀ j (hj : (j, s.input.n + f) ∈ q.ps),
--         (q.packing.label (planIndex q.ps s.input.n f j hj)).slot 0 s.input.node = color f)
--       (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
--         ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
--           l.variable ∉ H → (l.variable.val, s.input.n + id) ∈ q.ps)
--       (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
--         ∀ l ∈ q.markedClause, l.variable ∉ H →
--           (l.variable.val, s.input.n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
--    :
--       (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
--         ∑ U ∈ E.powerset, (-1) ^ (E.card - U.card) *
--           tupleTotal s.key s.input.r
--             (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts)) =
--         Truncated.ofPolynomial q.J ((specTarget q H high).comp
--           (X + C (q.p.ops.decode q.theta)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.planIndex` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instOneOfZero` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instPowNatOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.tupleTotal` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.node` (definitions bundle `OAIQ081S070` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.ofPolynomial` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.factorIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instNeg` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.weightedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.specTarget` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.emittedValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEmittedSourceTarget.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleSource
open SignatureTupleRun HeadSourceLocality BucketTupleProgram.Concrete

variable (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)

theorem signed_target (hu : q.u = q.p.t)
    (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
    (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
    (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t s.input.Q q.p.ht q.p.hfield s.input.node)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → Fin s.input.r)
    (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g))
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j, s.input.n + f) ∈ q.ps),
      (q.packing.label (planIndex q.ps s.input.n f j hj)).slot 0 s.input.node = color f)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, s.input.n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, s.input.n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
 :
    (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
      ∑ U ∈ E.powerset, (-1) ^ (E.card - U.card) *
        tupleTotal s.key s.input.r
          (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
end
end
