-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_outer_from_setup
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:18:55.288127+00:00
-- url     : https://prove2.me/theorems/ef3a8095-4812-42e7-8425-9e5a7550a4ba
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls DisjointReuse`):
--
--   ```lean
--   theorem outer_from_setup {n setupSteps inputBound bound : ℕ}
--       (k : ℕ) (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
--       (a b : State 80 1220)
--       (hsetup : DFSVisit.BoundedEval (setupAfterFrontend k) setupSteps a b inputBound)
--       (ready : SetupReady k F b) (hs : 0 < sparsifySchedule n)
--       (leaf : Cmd 80 1220) (leafTime : ℕ)
--       (hstartup : 1220 * inputBound +
--         8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
--       (hvisit : DFSCountProgram.visitSpace k n F.card (b.stacks 259).length ≤ bound)
--       (hleaf : DFSVisit.LeafContract (n := n) k (b.stacks 259) inputBound
--         leaf leafTime bound) :
--       ∃ visits total final,
--         total ≤ setupSteps +
--           dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
--             (b.stacks 259).length leafTime bound visits +
--           12 * outerBoundary inputBound bound n + 14 ∧
--         DFSVisit.BoundedEval (outerCommand k leaf) total a final
--           (outerSpace inputBound bound n) ∧
--         final.stacks ABI.countStack = countWord (SAT.count F) ∧
--         final.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
--         (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) ∧
--         (visits : ℝ) ≤
--           ((SparseCharging.depthConstant k
--             (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
--             (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.answerStack` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.countStack` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.depthConstant` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Satisfiable` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.visitSpace` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.dfsTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.SetupReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafContract` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerCommand` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.CNF`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause`, `OAI.Algorithms.SubexponentialSAT.SAT.WidthAtMost`, `OAI.Algorithms.SubexponentialSAT.SAT.count` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

theorem outer_from_setup {n setupSteps inputBound bound : ℕ}
    (k : ℕ) (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a b : State 80 1220)
    (hsetup : DFSVisit.BoundedEval (setupAfterFrontend k) setupSteps a b inputBound)
    (ready : SetupReady k F b) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime : ℕ)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card (b.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (b.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits total final,
      total ≤ setupSteps +
        dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
          (b.stacks 259).length leafTime bound visits +
        12 * outerBoundary inputBound bound n + 14 ∧
      DFSVisit.BoundedEval (outerCommand k leaf) total a final
        (outerSpace inputBound bound n) ∧
      final.stacks ABI.countStack = countWord (SAT.count F) ∧
      final.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
