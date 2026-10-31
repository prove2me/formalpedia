-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly_metadata_searches
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:19:38.118785+00:00
-- url     : https://prove2.me/theorems/fda344dd-6a35-4bdf-854e-2d4d16785a31
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCodeAssembly.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCodeAssembly.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly`, with `open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage`):
--
--   ```lean
--   theorem metadata_searches {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
--       (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
--       (ha : ∀ i, (a.stacks i).length ≤ A) :
--       ∃ (steps : ℕ) (out : Data)
--         (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
--         (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
--         steps ≤ NativeCode.searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
--         Eval NativeCode.searches steps a out ∧ out.stacks 816 = CodeSearchProgram.matrixFrames shifts ∧
--         out.stacks 815 = CodeSearchProgram.matrixFrames Q ∧
--         WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
--         SparseCode.HasDistance Q
--           (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
--         (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
--         (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ NativeCode.searchBoundary A m occurrence) ∧
--         ∀ k c, k ≤ steps → Trace (compiled NativeCode.searches 784 788) k
--           (a.withPC (some (compiled NativeCode.searches 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤ NativeCode.searchesSpace A m occurrence
--             (a.stacks 800).length (a.stacks 801).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.searchBoundary` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.searchesSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.searchesTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.WorkerEmpty` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.searches` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeCodeAssembly.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem metadata_searches {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
    (ha : ∀ i, (a.stacks i).length ≤ A) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ NativeCode.searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval NativeCode.searches steps a out ∧ out.stacks 816 = CodeSearchProgram.matrixFrames shifts ∧
      out.stacks 815 = CodeSearchProgram.matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeCode.searchBoundary A m occurrence) ∧
      ∀ k c, k ≤ steps → Trace (compiled NativeCode.searches 784 788) k
        (a.withPC (some (compiled NativeCode.searches 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ NativeCode.searchesSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end
