-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_nonleaf_rel_step
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:20:12.45945+00:00
-- url     : https://prove2.me/theorems/7d5a2b21-99db-40e2-9c0b-1f02e2d38282
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete`, with `open Classical`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram`, `open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource`):
--
--   ```lean
--   theorem nonleaf_rel_step (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
--       {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
--       (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
--       (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
--       (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
--       (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
--       (step : Step s.key s.input.r event before after)
--       (ha : Rel s F q node H high E U P before acc a)
--       (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
--       a.regs controllerPorts.active=true ∧ ∃ steps b,
--         Iteration controllerPorts routines steps a b ∧
--         Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
--         steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
--         ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
--           (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
--           ∀ i,(z.stacks i).length ≤ prefixEnvelope s F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instAdd` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instZero` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS.Prefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.controllerPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Ports` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Event`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Representatives`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.callbackWeight` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.costWeight` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Iteration` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.eventPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.prefixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.Rel` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.routines` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step)

import Mathlib
import Definitions.Def_OAIQ081S191

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem nonleaf_rel_step (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (step : Step s.key s.input.r event before after)
    (ha : Rel s F q node H high E U P before acc a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
      steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end
