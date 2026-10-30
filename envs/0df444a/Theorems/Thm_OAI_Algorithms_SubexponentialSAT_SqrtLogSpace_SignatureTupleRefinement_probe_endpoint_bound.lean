-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_probe_endpoint_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:22:46.793563+00:00
-- url     : https://prove2.me/theorems/b1dafb86-ac88-4e83-9ac2-e5efc2bf1d17
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement`, with `open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem probe_endpoint_bound (a : State 40 896) (out : Fin 16 → Bool)
--       (W : List Bool) (rows : List (List (List Bool))) (h B F : ℕ)
--       (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
--       (hs : a.stacks remainingPorts.scratch = [])
--       (hlen : ∀ row ∈ rows, row.length = h)
--       (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
--       (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F)
--       (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F) :
--       ∀ i, ((probePostState a out W rows h candidate).stacks i).length ≤ F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Ports` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.keyBound` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.remainingPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.probePostState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound)

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

theorem probe_endpoint_bound (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h B F : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F) :
    ∀ i, ((probePostState a out W rows h candidate).stacks i).length ≤ F := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end
