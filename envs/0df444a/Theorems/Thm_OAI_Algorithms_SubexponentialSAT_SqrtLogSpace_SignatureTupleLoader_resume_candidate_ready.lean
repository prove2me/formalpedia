-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_resume_candidate_ready
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:20:53.297097+00:00
-- url     : https://prove2.me/theorems/fb6d1d04-b6b5-4173-b2e6-ec8317eabcc2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader`, with `open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement`, `open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem resume_candidate_ready (a : State 40 896) (W : List Bool)
--       (rows : List (List (List Bool))) (h : ℕ)
--       (candidate next : Fin (2^h)) (hnext : next.val=candidate.val+1)
--       (hw : CursorWords a h candidate.val)
--       (hW : a.stacks 141=W)
--       (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words))
--       (hh : a.stacks 651=List.replicate h false)
--       (hk : a.stacks (tupleStacks 3)=[]) (hz : a.stacks (tupleStacks 8)=[])
--       (hscratch : ∀ i : Fin 24, i≠0 → i≠15 → i≠16 → i≠17 → i≠18 → i≠22 →
--         a.stacks (rescanStacks i)=[]) :
--       CandidateReady (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)) W rows h next
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.rescanStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.tupleStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.copyState` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CursorWords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.advanceCandidateState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoader.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready)

import Mathlib
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Storage
open SignatureTupleDFS SignatureTupleTraversal

theorem resume_candidate_ready (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ)
    (candidate next : Fin (2^h)) (hnext : next.val=candidate.val+1)
    (hw : CursorWords a h candidate.val)
    (hW : a.stacks 141=W)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words))
    (hh : a.stacks 651=List.replicate h false)
    (hk : a.stacks (tupleStacks 3)=[]) (hz : a.stacks (tupleStacks 8)=[])
    (hscratch : ∀ i : Fin 24, i≠0 → i≠15 → i≠16 → i≠17 → i≠18 → i≠22 →
      a.stacks (rescanStacks i)=[]) :
    CandidateReady (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)) W rows h next := by
  sorry

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end
