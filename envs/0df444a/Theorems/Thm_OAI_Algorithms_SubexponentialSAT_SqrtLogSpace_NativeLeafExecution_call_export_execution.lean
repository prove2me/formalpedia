-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafExecution_call_export_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:51.748706+00:00
-- url     : https://prove2.me/theorems/b01eae3e-e8e5-412b-b66d-df374f7b96cb
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit`):
--
--   ```lean
--   theorem call_export_execution (localCommand : Cmd 40 896) (a : Data) (b : LocalData)
--       {steps localBound B : ℕ}
--       (he : Eval localCommand steps (projectState ABI.leafRegisters ABI.leafStacks a) b)
--       (hp : ∀ q z, q ≤ steps →
--         Trace (compiled localCommand 784 788) q
--           ((projectState ABI.leafRegisters ABI.leafStacks a).withPC
--             (some (compiled localCommand 784 788).entry)) z →
--         ∀ i, (z.stacks i).length ≤ localBound)
--       (ha : ∀ i, (a.stacks i).length ≤ B) (hB : localBound ≤ B) :
--       ∃ t ≤ steps + 1803 * B + 2700, ∃ e,
--         BoundedEval (.seq (ABI.leafCall (compiled localCommand 784 788)) Native.exportLeaf)
--           t a e B ∧
--         e.stacks 263 = b.stacks 788 ∧ e.stacks 1219 = [] ∧
--         (∀ j, e.stacks (ABI.leafStacks j) = []) ∧
--         (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
--           e.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.leafRegisters` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.leafStacks` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.leafCall` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.exportLeaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.LocalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution

open BitProgram StructuredCalls DisjointReuse DFSVisit

theorem call_export_execution (localCommand : Cmd 40 896) (a : Data) (b : LocalData)
    {steps localBound B : ℕ}
    (he : Eval localCommand steps (projectState ABI.leafRegisters ABI.leafStacks a) b)
    (hp : ∀ q z, q ≤ steps →
      Trace (compiled localCommand 784 788) q
        ((projectState ABI.leafRegisters ABI.leafStacks a).withPC
          (some (compiled localCommand 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ localBound)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hB : localBound ≤ B) :
    ∃ t ≤ steps + 1803 * B + 2700, ∃ e,
      BoundedEval (.seq (ABI.leafCall (compiled localCommand 784 788)) Native.exportLeaf)
        t a e B ∧
      e.stacks 263 = b.stacks 788 ∧ e.stacks 1219 = [] ∧
      (∀ j, e.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
        e.stacks i = a.stacks i) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution
end
