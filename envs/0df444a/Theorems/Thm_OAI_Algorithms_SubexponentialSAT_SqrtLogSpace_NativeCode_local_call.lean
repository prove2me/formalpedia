-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCode_local_call
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:19:15.39497+00:00
-- url     : https://prove2.me/theorems/85593ac0-2972-4d35-9001-ad6167b908f5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode`, with `open BitProgram StructuredCalls`, `open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem local_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
--       (A : ℕ) (a : Data)
--       (hready : CodeChecks.LocalMatrixReady (SparseCode.localRows m occurrence)
--         (SparseCode.degree m occurrence)
--         (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)
--         (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
--       (ha : ∀ i, (a.stacks i).length ≤ A)
--       (hdim : a.stacks 46 = List.replicate
--         (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
--       (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
--       ∃ (steps : ℕ) (out : Data)
--         (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
--         steps ≤ SparseCodeSearch.localTime A (SparseCode.localRows m occurrence)
--           (SparseCode.degree m occurrence)
--           (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 ∧
--         Eval localCall steps a out ∧ out.stacks 18 = matrixFrames Q ∧
--         SparseCode.HasDistance Q
--           (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
--         (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
--           (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
--         ∀ k c, k ≤ steps → Trace (compiled localCall 784 788) k
--           (a.withPC (some (compiled localCall 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max
--             (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
--               (SparseCode.degree m occurrence)
--               (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.leafRegisters` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.leafStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.localSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.localTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.LocalMatrixReady` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.localCall` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

theorem local_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data)
    (hready : CodeChecks.LocalMatrixReady (SparseCode.localRows m occurrence)
      (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ SparseCodeSearch.localTime A (SparseCode.localRows m occurrence)
        (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 ∧
      Eval localCall steps a out ∧ out.stacks 18 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled localCall 784 788) k
        (a.withPC (some (compiled localCall 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
            (SparseCode.degree m occurrence)
            (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end
