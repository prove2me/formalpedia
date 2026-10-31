-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_callback_eval_correct
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:03:40.298092+00:00
-- url     : https://prove2.me/theorems/0b449479-91f7-405a-8b47-10da2e92a67f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics`, `open FactorAssignmentProgram`, `open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram`):
--
--   ```lean
--   theorem callback_eval_correct (h : Input q A S one seed a f)
--       (hone : NativeSemantics.Good ∅ q.u q.J one)
--       (hseed : NativeSemantics.Good ∅ q.u q.J seed)
--       (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
--         Squarefree.canonical q.u q.J 1)
--       (width : ℕ)
--       (hwidth : ∀ hf : f < q.rows.length,
--         ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
--           w.literals.length ≤ width) :
--       ∃ (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
--         (rf : Fin 8 → Bool) (steps : ℕ) (z : FactorAssignmentProgram.Data),
--         NativeSemantics.Good ∅ q.u q.J out ∧
--         TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
--           TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
--             QueryEvaluation.specializeDense q.u q.J
--               (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
--               (q.value (a.stacks ∘ lowStack) f) ∧
--         steps ≤ callbackBudget q A S width a f rf ∧
--         Eval FactorAssignmentProgram.callback steps a z ∧
--         z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
--         z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.decodeMask` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation.specializeDense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.rawDenote` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.Raw` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.rawValue` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.value` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callbackBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.callback` (definitions bundle `OAIQ081S189` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

theorem callback_eval_correct (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (width : ℕ)
    (hwidth : ∀ hf : f < q.rows.length,
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width) :
    ∃ (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (rf : Fin 8 → Bool) (steps : ℕ) (z : FactorAssignmentProgram.Data),
      NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
            (q.value (a.stacks ∘ lowStack) f) ∧
      steps ≤ callbackBudget q A S width a f rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end
