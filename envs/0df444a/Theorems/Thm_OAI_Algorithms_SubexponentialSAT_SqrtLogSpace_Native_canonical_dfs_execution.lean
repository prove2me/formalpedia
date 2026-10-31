-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_canonical_dfs_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:48:14.378019+00:00
-- url     : https://prove2.me/theorems/c8ee5c0d-68d1-4512-89ad-2c2d34964f81
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls BinaryArithmetic DisjointReuse`):
--
--   ```lean
--   theorem canonical_dfs_execution {n : ℕ} (k : ℕ) (hk : 2 ≤ k)
--       (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
--       (a : State 80 1220) (ready : SetupReady k F a) (hs : 0 < sparsifySchedule n)
--       (leaf : Cmd 80 1220) (leafTime inputBound bound : ℕ)
--       (hinput : ∀ i, (a.stacks i).length ≤ inputBound)
--       (hstartup : 1220 * inputBound +
--         8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
--       (hvisit : DFSCountProgram.visitSpace k n F.card
--         (a.stacks 259).length ≤ bound)
--       (hleaf : DFSVisit.LeafContract (n := n) k (a.stacks 259) inputBound
--         leaf leafTime bound) :
--       ∃ visits t b,
--         t ≤ 8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 16 +
--           (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
--             (a.stacks 259).length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
--         DFSVisit.BoundedEval (DFSCountProgram.command k leaf) t a b
--           (1224 * bound + 7 * n + 19) ∧
--         b.stacks 256 = countWord (SAT.count F) ∧
--         (visits : ℝ) ≤
--           ((SparseCharging.depthConstant k
--             (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
--             (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.depthConstant` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.visitSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.visitTime` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.SetupReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafContract` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.CNF`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause`, `OAI.Algorithms.SubexponentialSAT.SAT.WidthAtMost`, `OAI.Algorithms.SubexponentialSAT.SAT.count` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem canonical_dfs_execution {n : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a : State 80 1220) (ready : SetupReady k F a) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime inputBound bound : ℕ)
    (hinput : ∀ i, (a.stacks i).length ≤ inputBound)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card
      (a.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (a.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits t b,
      t ≤ 8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 16 +
        (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
          (a.stacks 259).length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
      DFSVisit.BoundedEval (DFSCountProgram.command k leaf) t a b
        (1224 * bound + 7 * n + 19) ∧
      b.stacks 256 = countWord (SAT.count F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
