-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_Input_staged_factorJet
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:26:55.955161+00:00
-- url     : https://prove2.me/theorems/e981bba5-0e80-4118-8d1e-3a2edaae9799
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics`, `open FactorAssignmentProgram`, `open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram`):
--
--   ```lean
--   theorem Input.staged_factorJet (h : Input q A S one seed a f)
--       (rf : Fin 8 → Bool) (j : ℕ) :
--       PerturbationAssembly.sourceIncidenceJet q.p q.ps q.packing n f j q.theta
--         (FactorTableProgram.projectBase
--           (FactorTableProgram.staged
--             (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks) =
--         Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.lowStack` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectBase` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.Raw` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.tableInput` (definitions bundle `OAIQ081S164` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.staged` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.fetched` (definitions bundle `OAIQ081S177` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceIncidenceJet` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.factorJet` (definitions bundle `OAIQ081S181` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallbackNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet)

import Mathlib
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S177
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S181

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem Input.staged_factorJet (h : Input q A S one seed a f)
    (rf : Fin 8 → Bool) (j : ℕ) :
    PerturbationAssembly.sourceIncidenceJet q.p q.ps q.packing n f j q.theta
      (FactorTableProgram.projectBase
        (FactorTableProgram.staged
          (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks) =
      Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end
