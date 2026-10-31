-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_resume_loaded_storage
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:22:46.713987+00:00
-- url     : https://prove2.me/theorems/5aa7817e-9ae0-4fa3-a599-c079b0b744f5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement`, with `open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem resume_loaded_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
--       (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
--       (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ) (a : State 40 896)
--       (ha : AncestorStorage h key levels base depth.val ancestors a)
--       (hw : CursorWords a (h depth.val) candidate) (hc : candidate < 2 ^ h depth.val)
--       (hleaf : a.regs controllerPorts.leaf = false)
--       (hwidth : a.stacks 651 = List.replicate (h depth.val) false)
--       (hp : a.stacks (tupleStacks 4) = []) (hz : a.stacks (tupleStacks 8) = []) :
--       ScanStorage h key levels base depth ancestors (candidate + 1)
--         (advanceCandidateState (copyState 651 (tupleStacks 8) a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS.Prefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.controllerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.tupleStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Ports` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal.Representatives` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.AncestorStorage` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.copyState` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CursorWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.ScanStorage` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.advanceCandidateState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage)

import Mathlib
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem resume_loaded_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ) (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) candidate) (hc : candidate < 2 ^ h depth.val)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hwidth : a.stacks 651 = List.replicate (h depth.val) false)
    (hp : a.stacks (tupleStacks 4) = []) (hz : a.stacks (tupleStacks 8) = []) :
    ScanStorage h key levels base depth ancestors (candidate + 1)
      (advanceCandidateState (copyState 651 (tupleStacks 8) a)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end
