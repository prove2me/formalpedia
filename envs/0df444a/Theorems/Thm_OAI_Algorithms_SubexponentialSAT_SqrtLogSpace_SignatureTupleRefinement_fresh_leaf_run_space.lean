-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_fresh_leaf_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:22:08.453365+00:00
-- url     : https://prove2.me/theorems/3b6d3411-ae91-4656-99e3-7add78768993
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement`, with `open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative`, `open SignatureTupleDFS SignatureTupleTraversal`):
--
--   ```lean
--   theorem fresh_leaf_run_space (loadHead visit : Cmd 40 896) (a : State 40 896)
--       (W : List Bool) (rows : List (List (List Bool))) (h B F address : ℕ)
--       (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
--       (hw : CursorWords a h candidate.val)
--       (hlen : ∀ row ∈ rows, row.length = h)
--       (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
--       (hleaf : a.regs controllerPorts.leaf = false)
--       (hfresh : Bool.not (AttainedSignatures.duplicateScan
--         (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) = true)
--       (hpayload : a.stacks (tupleStacks 4) = [])
--       (hheads : a.stacks (tupleStacks 6) = [true])
--       (haddress : a.stacks (tupleStacks 9) = List.replicate address true)
--       (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F) (hcursor : h + 1 ≤ F)
--       (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F)
--       (hspace : AttainedSignatureProgram.Rescan.spaceBudget W rows h B ≤ F) :
--       ∃ n out,
--         Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
--           (descendClearState (probePostState a out W rows h candidate)) ∧
--         (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
--           Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
--             prefixSteps (a.withPC (some (compiled
--               (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
--         n + 1 ≤ (candidate.val + 1) *
--           (AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 64 * F + 100)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.duplicateScan` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.controllerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.tupleStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Ports` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.keyBound` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.polynomialBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.spaceBudget` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.assembleRoutines` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.candidateCall` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.descendClearState` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CursorWords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.probePostState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRefinement.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space)

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

theorem fresh_leaf_run_space (loadHead visit : Cmd 40 896) (a : State 40 896)
    (W : List Bool) (rows : List (List (List Bool))) (h B F address : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hfresh : Bool.not (AttainedSignatures.duplicateScan
      (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) = true)
    (hpayload : a.stacks (tupleStacks 4) = [])
    (hheads : a.stacks (tupleStacks 6) = [true])
    (haddress : a.stacks (tupleStacks 9) = List.replicate address true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F) (hcursor : h + 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F)
    (hspace : AttainedSignatureProgram.Rescan.spaceBudget W rows h B ≤ F) :
    ∃ n out,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (descendClearState (probePostState a out W rows h candidate)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ (candidate.val + 1) *
        (AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 64 * F + 100) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end
