-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCode_graph_call
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:18:27.368846+00:00
-- url     : https://prove2.me/theorems/edf39519-08be-482e-ae83-7f66273b1524
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode`, with `open BitProgram StructuredCalls`, `open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem graph_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
--       (A : ℕ) (a : Data)
--       (hq : BinaryArithmetic.toNat (a.stacks 31) = SparseCode.gapDenom m occurrence)
--       (hD : BinaryArithmetic.toNat (a.stacks 32) = SparseCode.degree m occurrence)
--       (hready : CodeChecks.GraphMatrixReady (SparseCode.degree m occurrence)
--         (SparseCode.dimension m occurrence) (a.stacks 31) (a.stacks 32)
--         (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
--       (ha : ∀ i, (a.stacks i).length ≤ A)
--       (hdim : a.stacks 46 = List.replicate
--         (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true)
--       (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
--       ∃ (steps : ℕ) (out : Data)
--         (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
--         steps ≤ SparseCodeSearch.graphTime A (SparseCode.degree m occurrence)
--           (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length + 1 ∧
--         Eval graphCall steps a out ∧ out.stacks 29 = matrixFrames Q ∧
--         WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
--         (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
--           (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
--         ∀ k c, k ≤ steps → Trace (compiled graphCall 784 788) k
--           (a.withPC (some (compiled graphCall 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max
--             (SparseCodeSearch.graphSpace A (SparseCode.degree m occurrence)
--               (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length) A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.leafRegisters` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.leafStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graphSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graphTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.GraphMatrixReady` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graphCall` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

theorem graph_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data)
    (hq : BinaryArithmetic.toNat (a.stacks 31) = SparseCode.gapDenom m occurrence)
    (hD : BinaryArithmetic.toNat (a.stacks 32) = SparseCode.degree m occurrence)
    (hready : CodeChecks.GraphMatrixReady (SparseCode.degree m occurrence)
      (SparseCode.dimension m occurrence) (a.stacks 31) (a.stacks 32)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
      steps ≤ SparseCodeSearch.graphTime A (SparseCode.degree m occurrence)
        (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length + 1 ∧
      Eval graphCall steps a out ∧ out.stacks 29 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
      (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled graphCall 784 788) k
        (a.withPC (some (compiled graphCall 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (SparseCodeSearch.graphSpace A (SparseCode.degree m occurrence)
            (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length) A := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end
