-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge_probe_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:21:37.573189+00:00
-- url     : https://prove2.me/theorems/94295f04-6b28-4cc1-a002-bf90e4d41086
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureRescanBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureRescanBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge`, with `open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative`, `open AttainedSignatureProgram.Rescan`):
--
--   ```lean
--   theorem probe_run_space (a : State 40 896) (W : List Bool)
--       (rows : List (List (List Bool))) (h B frameBound : ℕ)
--       (hlen : ∀ row ∈ rows, row.length = h)
--       (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
--       (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
--       (hs : a.stacks remainingPorts.scratch = [])
--       (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false)
--       (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
--       ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B +
--           8 * (a.stacks remainingPorts.counter).length +
--           2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
--         Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
--           Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
--             (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             896 * (spaceBudget W rows h B + frameBound + 1) +
--               8 * (a.stacks remainingPorts.counter).length +
--               2 * (a.stacks (rescanStacks 22)).length + 20
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.isZero` and `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Ports` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.rescanStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.polynomialBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.spaceBudget` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.candidateCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.probeWith` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.remainingPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.probePostState` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureRescanBridge.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space)

import Mathlib
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

theorem probe_run_space (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B frameBound : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B +
        8 * (a.stacks remainingPorts.counter).length +
        2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
      Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
          (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * (spaceBudget W rows h B + frameBound + 1) +
            8 * (a.stacks remainingPorts.counter).length +
            2 * (a.stacks (rescanStacks 22)).length + 20 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end
