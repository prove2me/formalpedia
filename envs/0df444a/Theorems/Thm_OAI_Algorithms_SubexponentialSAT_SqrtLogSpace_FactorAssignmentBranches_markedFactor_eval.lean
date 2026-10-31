-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches_markedFactor_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:03:09.92423+00:00
-- url     : https://prove2.me/theorems/1e02665e-1b56-4740-b379-998facd726b6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBranches.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBranches.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics`, `open FactorAssignmentProgram`, `open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram`):
--
--   ```lean
--   theorem markedFactor_eval {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
--       (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
--       (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
--       (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
--       (ls : List (SAT.Literal (Fin n))) (a : FactorAssignmentProgram.Data)
--       (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
--       (h556 : a.stacks 556 = []) (h359 : a.stacks 359 = []) (h62 : a.stacks 62 = [])
--       (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
--       (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
--       (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
--       (houtput : a.stacks 63 = [])
--       (hlow : ∀ i, a.stacks (lowStack (Clause.callerStacks (Memory.lowPort i))) = low ctx i)
--       (honeTape : a.stacks 69 = Product.bytes one)
--       (hminus : a.stacks 76 = RingProgram.flat minus)
--       (hwork : ∀ i ∈ FactorServices.clauseScratch,
--         a.stacks (lowStack (Clause.callerStacks i)) = [])
--       (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
--       ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
--         (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
--         (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
--           (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
--         let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
--           (FactorServices.clauseResult ctx minus one incidence ls) []
--         steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
--           (9 * (a.stacks 154).length + 9 +
--             FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J ls.length 0 0) ∧
--         Good ∅ ctx.u ctx.J result ∧
--         Eval FactorAssignmentProgram.markedFactor steps a e ∧
--         e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.lowPort` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.callerStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseScratch` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.serviceBudget` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.writtenPorts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.literalBits` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseResult` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.tableInput` (definitions bundle `OAIQ081S164` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.staged` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.PayloadMeaning` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.tableTime` (definitions bundle `OAIQ081S184` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.markedFactor` (definitions bundle `OAIQ081S189` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBranches.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

theorem markedFactor_eval {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ctx : Context 3 p.t n d) (f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (ls : List (SAT.Literal (Fin n))) (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556 = []) (h359 : a.stacks 359 = []) (h62 : a.stacks 62 = [])
    (hready : FactorTableNative.Ready p ps P ctx.u ctx.J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = [])
    (hraw : a.stacks 154 = Encoding.encodeList id (ls.map Clause.literalBits))
    (houtput : a.stacks 63 = [])
    (hlow : ∀ i, a.stacks (lowStack (Clause.callerStacks (Memory.lowPort i))) = low ctx i)
    (honeTape : a.stacks 69 = Product.bytes one)
    (hminus : a.stacks 76 = RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,
      a.stacks (lowStack (Clause.callerStacks i)) = [])
    (hseedTape : a.stacks 151 = Product.bytes seed) (htmp : a.stacks 159 = []) :
    ∃ (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ ctx.u ctx.J (incidence v)) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P ctx.u ctx.J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      let result := Product.run 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
        (FactorServices.clauseResult ctx minus one incidence ls) []
      steps ≤ 7 * (f + 1) + 7 + tableTime p ctx.u ctx.J n B S a f +
        (9 * (a.stacks 154).length + 9 +
          FactorEvaluationSpace.serviceBudget (baseWidth 3 p.t) d n ctx.u ctx.J ls.length 0 0) ∧
      Good ∅ ctx.u ctx.J result ∧
      Eval FactorAssignmentProgram.markedFactor steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 154 []) 151 (Product.bytes result) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end
