-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_exhausted_successor_step
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:20:24.610393+00:00
-- url     : https://prove2.me/theorems/9ced9deb-3d6b-45b9-a6d7-4186747f249f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete`, with `open Classical`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram`, `open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource`):
--
--   ```lean
--   theorem exhausted_successor_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
--       (visit : Cmd 40 896) (depth : Fin s.input.r) (hd : depth.val + 1 < s.input.r)
--       (ancestors : Prefix (Representatives s.key) (depth.val+1)) (a : State 40 896)
--       (ha : ScanBoundary s F ⟨depth.val+1,hd⟩ ancestors (2^s.headSize (depth.val+1)) a) :
--       ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
--         ScanBoundary s F depth (Fin.init ancestors)
--           ((ancestors (Fin.last depth.val)).val.val+1) b ∧
--         n+1 ≤ eventPolynomial s F ∧
--         (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
--           (assembleRoutines loadHead candidateCall visit)) 0 0) p
--           (a.withPC (some (compiled (body controllerPorts
--             (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
--           ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.PersistentPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS.Prefix` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.controllerPorts` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Representatives` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.assembleRoutines` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.candidateCall` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Iteration` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.eventPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.prefixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.headSize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource.ProducedSource.key` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ScanBoundary` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.loadHead` (definitions bundle `OAIQ081S191` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleComplete.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step)

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

theorem exhausted_successor_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r) (hd : depth.val + 1 < s.input.r)
    (ancestors : Prefix (Representatives s.key) (depth.val+1)) (a : State 40 896)
    (ha : ScanBoundary s F ⟨depth.val+1,hd⟩ ancestors (2^s.headSize (depth.val+1)) a) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end
