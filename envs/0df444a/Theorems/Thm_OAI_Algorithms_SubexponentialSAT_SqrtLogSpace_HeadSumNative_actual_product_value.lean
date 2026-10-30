-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_actual_product_value
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:57:27.659182+00:00
-- url     : https://prove2.me/theorems/6984425d-38cf-4a3f-a75e-cd2755b18fe4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative`, with `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram`, `open HeadIdentifierProgram BucketTupleProgram.Concrete`, `open QueryTupleState (masterPorts QueryMasterFrame QueryReady)`, `open scoped BigOperators`):
--
--   ```lean
--   theorem actual_product_value {r Q n d : ℕ} (q : Factor.Spec r Q n d)
--       (H : Finset (Fin n)) (high : H → Bool) (U : Finset (Fin n))
--       (x : ResidualEmbedding.Free H → Bool) (a : HeadSumProgram.Data) (ids : List ℕ)
--       (hmask : a.stacks 702 = List.ofFn (fun v : Fin n => decide (v ∈ H)))
--       (hbits : a.stacks 703 = List.ofFn (fun v : Fin n => if h : v ∈ H then high ⟨v,h⟩ else false))
--       (hU : a.stacks 857 = List.ofFn (fun v : Fin n => decide (v ∈ U)))
--       (h145 : a.stacks 145 = List.ofFn (HighIncidence.glue H high x))
--       (hzero : ∀ id j (v : Fin n), v ∈ H →
--         PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0) :
--       QueryEvaluation.specializeDense q.u q.J
--         (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
--         (Squarefree.canonical q.u q.J
--           ((ids.map (q.value (a.stacks ∘ FactorAssignmentProgram.lowStack))).prod)) =
--       QueryEvaluation.specializeDense q.u q.J
--         (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
--         (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high x) ids)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.decodeMask` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.stateFor` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation.specializeDense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.fixedSourceRow` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.value` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.sourceProduct` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame QueryReady)
open scoped BigOperators

noncomputable section

theorem actual_product_value {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (U : Finset (Fin n))
    (x : ResidualEmbedding.Free H → Bool) (a : HeadSumProgram.Data) (ids : List ℕ)
    (hmask : a.stacks 702 = List.ofFn (fun v : Fin n => decide (v ∈ H)))
    (hbits : a.stacks 703 = List.ofFn (fun v : Fin n => if h : v ∈ H then high ⟨v,h⟩ else false))
    (hU : a.stacks 857 = List.ofFn (fun v : Fin n => decide (v ∈ U)))
    (h145 : a.stacks 145 = List.ofFn (HighIncidence.glue H high x))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0) :
    QueryEvaluation.specializeDense q.u q.J
      (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
      (Squarefree.canonical q.u q.J
        ((ids.map (q.value (a.stacks ∘ FactorAssignmentProgram.lowStack))).prod)) =
    QueryEvaluation.specializeDense q.u q.J
      (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
      (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high x) ids) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end
