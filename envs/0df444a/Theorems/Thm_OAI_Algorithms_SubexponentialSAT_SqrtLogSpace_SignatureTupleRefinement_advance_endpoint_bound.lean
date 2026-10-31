-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_advance_endpoint_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:21:28.468973+00:00
-- url     : https://prove2.me/theorems/fe9d60fc-90a1-4aab-b32a-1cbae2139eae
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement`, with `open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem advance_endpoint_bound (a : State 40 896) (h candidate F : ℕ)
--       (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
--       (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
--       ∀ i, ((advanceCandidateState a).stacks i).length ≤ F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CursorWords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.advanceCandidateState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound)

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

theorem advance_endpoint_bound (a : State 40 896) (h candidate F : ℕ)
    (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
    ∀ i, ((advanceCandidateState a).stacks i).length ≤ F := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end
