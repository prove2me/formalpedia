-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorHead_head_multiply_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:16:31.660958+00:00
-- url     : https://prove2.me/theorems/24b8d97d-0a52-4f7d-9f1e-98d439c5a495
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram`, `open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage`, `open scoped BigOperators`):
--
--   ```lean
--   theorem head_multiply_run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
--       (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
--       (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
--       (g : Fin r) (pick : ℕ → Bool)
--       (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
--       (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
--       (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
--       (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
--         (BinaryArithmetic.toNat W : ℤ) +
--           LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
--             ((chosenIds pick n).get i))
--       (ids : List ℕ) (a : HeadSumProgram.Data)
--       (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
--       (hshape : a.stacks 651 = List.replicate (count pick n) false)
--       (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
--       (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
--         (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
--       (hW : a.stacks 864 = W)
--       (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
--         ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
--       (hkey : a.stacks 866 = BucketProgram.signatureValue W
--         (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
--           (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
--         (List.ofFn (fun j => List.ofFn (c j))))
--       (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
--         (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
--       (hH : a.stacks 868 = List.replicate (count pick n) true)
--       (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
--       (hzero : ∀ id j (v : Fin n), v ∈ H →
--         PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
--       (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
--       (hcoeff : ∀ j i, (c j i).length  ≤  P)
--       (hcache : 4*M+6  ≤  P)
--       (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
--       (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
--         (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
--       (hradius : q.p.R+1  ≤  Q) (width : ℕ)
--       (hwidth : ∀ f (hf : f < q.rows.length),
--         ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
--           w.literals.length  ≤  width)
--       (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
--       (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
--       (hhashScale : ∀ f (hf : f < q.rows.length),
--         FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
--           width q.rows[f].length q.digits.length  ≤  Z)
--       (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
--         q.markedClause.length 0 0  ≤  Z)
--       (B : ℕ)
--       (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
--         HeadAcceptedCorrect.budget q P S Z  ≤  B)
--       (hcounter : 9*(count pick n+1)+8  ≤  B)
--       {pairValue : Truncated (q.p.model.O q.p.t) q.J}
--       {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
--       (hpair : PairAccumulatorMeaning q pairValue a)
--       (htuple : DenseWord q 852 tupleValue a)
--       (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P) :
--       ∃ steps b,
--         Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
--           QueryAssembler.TupleMultiply.command) steps a b ∧
--         QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
--         DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
--         b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
--         (∀ i∈retainedPorts,b.stacks i=a.stacks i) ∧
--         (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
--         steps ≤ sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
--         QueryExecution.PrefixBound (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
--           QueryAssembler.TupleMultiply.command) steps a (max B (896*P+multiplyBudget q P))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Head` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.inputScale`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.byteBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalRecordBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.retainedPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyPolynomial` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureValue`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete.freeAssignmentEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.chosenIds_nodup` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.assemble` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.records` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.head` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.TupleMultiply.command` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.digits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.fixedSourceRow` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.DenseWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.PairAccumulatorMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryMasterFrame` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.multiplyBudget` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.headValue` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.sumBudget` (definitions bundle `OAIQ081S191` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem head_multiply_run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 864 = W)
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
    (hcoeff : ∀ j i, (c j i).length  ≤  P)
    (hcache : 4*M+6  ≤  P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
    (hradius : q.p.R+1  ≤  Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length  ≤  width)
    (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
    (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length  ≤  Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0  ≤  Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z  ≤  B)
    (hcounter : 9*(count pick n+1)+8  ≤  B)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a)
    (htuple : DenseWord q 852 tupleValue a)
    (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P) :
    ∃ steps b,
      Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a b ∧
      QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
      b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈retainedPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
      QueryExecution.PrefixBound (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a (max B (896*P+multiplyBudget q P)) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end
