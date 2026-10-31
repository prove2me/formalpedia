-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_parameters_trace_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:00:33.907111+00:00
-- url     : https://prove2.me/theorems/353cd3e1-d0e8-43ac-a9a6-8e57bfeffcb2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafSetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafSetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup`, with `open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram`):
--
--   ```lean
--   theorem parameters_trace_space (a : Data) {m B W : ℕ} (hm : 0 < m) (hB : 0 < B)
--       (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782) = m)
--       (hBv : BinaryArithmetic.toNat (a.stacks 786) = B)
--       (hW : ∀ i, (a.stacks i).length ≤ W) :
--       ∃ steps b, steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length ∧
--         Eval parameters steps a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i = false) ∧
--         Metadata m B b ∧
--         (b.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
--         (b.stacks 801).length ≤ 4 * (a.stacks 782).length + 2 * (a.stacks 786).length + 30 ∧
--         (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) →
--           b.stacks i = a.stacks i) ∧
--         (∀ i, (b.stacks i).length ≤
--           W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length) ∧
--         Trace (compiled parameters 784 788) (steps + 1)
--           (a.withPC (some (compiled parameters 784 788).entry)) (b.withPC none) ∧
--         ∀ k c, k ≤ steps + 1 → Trace (compiled parameters 784 788) k
--           (a.withPC (some (compiled parameters 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤
--             W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.WorkerEmpty` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.parameters` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafSetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S172

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

theorem parameters_trace_space (a : Data) {m B W : ℕ} (hm : 0 < m) (hB : 0 < B)
    (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBv : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hW : ∀ i, (a.stacks i).length ≤ W) :
    ∃ steps b, steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length ∧
      Eval parameters steps a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i = false) ∧
      Metadata m B b ∧
      (b.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
      (b.stacks 801).length ≤ 4 * (a.stacks 782).length + 2 * (a.stacks 786).length + 30 ∧
      (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤
        W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length) ∧
      Trace (compiled parameters 784 788) (steps + 1)
        (a.withPC (some (compiled parameters 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled parameters 784 788) k
        (a.withPC (some (compiled parameters 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length + 1 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end
