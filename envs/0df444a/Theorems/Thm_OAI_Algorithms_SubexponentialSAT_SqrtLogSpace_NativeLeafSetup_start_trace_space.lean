-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_start_trace_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:20:08.302834+00:00
-- url     : https://prove2.me/theorems/08466dd0-8aa4-4c6d-a3f3-15312ca0b224
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup`, with `open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram`):
--
--   ```lean
--   theorem start_trace_space (a : Data) (W : ℕ) (records : List (List Bool))
--       (hW : ∀ i, (a.stacks i).length ≤ W)
--       (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
--       (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ []) :
--       ∃ steps b, steps ≤ startBudget W records ∧
--         steps ≤ CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 ∧
--         Eval start steps a b ∧
--         StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
--           (BinaryArithmetic.toNat (a.stacks 786)) ∧
--         (∀ i : Fin 896, 784 ≤ i.val → b.stacks i = a.stacks i) ∧
--         (∀ i, (b.stacks i).length ≤ W + startBudget W records) ∧
--         Trace (compiled start 784 788) (steps + 1)
--           (a.withPC (some (compiled start 784 788).entry)) (b.withPC none) ∧
--         ∀ k c, k ≤ steps + 1 → Trace (compiled start 784 788) k
--           (a.withPC (some (compiled start 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤
--             W + CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCost.startupConstant` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.startBudget` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.StartReady` (definitions bundle `OAIQ081S126` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.start` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

theorem start_trace_space (a : Data) (W : ℕ) (records : List (List Bool))
    (hW : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ []) :
    ∃ steps b, steps ≤ startBudget W records ∧
      steps ≤ CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 ∧
      Eval start steps a b ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
        (BinaryArithmetic.toNat (a.stacks 786)) ∧
      (∀ i : Fin 896, 784 ≤ i.val → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + startBudget W records) ∧
      Trace (compiled start 784 788) (steps + 1)
        (a.withPC (some (compiled start 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled start 784 788) k
        (a.withPC (some (compiled start 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 + 1 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end
