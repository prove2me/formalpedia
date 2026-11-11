-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_shortcut_correct
-- name    : OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:40.466379+00:00
-- url     : https://prove2.me/theorems/dc00fd2a-a368-40ce-9ddc-e3ffdcca3803
-- title:
--   OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct` of [lean/OAI/Combinatorics/ThinTrees/Sparsification/ShortcutExtraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/ShortcutExtraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricTests.RationalStep`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions`, `open scoped MatrixOrder`):
--
--   ```lean
--   theorem shortcut_correct : ∃R : ℕ, 64^16 ≤ R ∧ ∀r : ℕ, R ≤ r →
--       ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
--         let a := extractState H r
--         a.realMatrix ∈ metricDomain H ∧ H.TreePackable a.active a.packingTarget ∧
--         0 < a.packingTarget ∧ a.packingTarget ≤ r ∧
--         (1-6*(r:ℝ)^(-1/16:ℝ))*r ≤ (a.packingTarget:ℝ) ∧
--         ∀e ∈ a.active, resistance H a.realMatrix e ≤ (r:ℝ)^(-1/4:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State.active` and `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State.packingTarget` (definitions bundle `OAIQ241TT001` of this split); `OAI.StrongThinTree.MultiGraph.TreePackable` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.extractState` (definitions bundle `OAIQ241TT005` of this split); `OAI.AlgorithmicThinTrees.MetricTests.metricDomain`, `OAI.AlgorithmicThinTrees.MetricTests.resistance` and `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.State.realMatrix` (definitions bundle `OAIQ241TT006` of this split); `OAI.StrongThinTree.MultiGraph` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proofs of `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial` and `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct` of this split import it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/ShortcutExtraction.lean (declaration OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT005
import Definitions.Def_OAIQ241TT006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

theorem shortcut_correct : ∃R : ℕ, 64^16 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      let a := extractState H r
      a.realMatrix ∈ metricDomain H ∧ H.TreePackable a.active a.packingTarget ∧
      0 < a.packingTarget ∧ a.packingTarget ≤ r ∧
      (1-6*(r:ℝ)^(-1/16:ℝ))*r ≤ (a.packingTarget:ℝ) ∧
      ∀e ∈ a.active, resistance H a.realMatrix e ≤ (r:ℝ)^(-1/4:ℝ) := by
  sorry

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end
