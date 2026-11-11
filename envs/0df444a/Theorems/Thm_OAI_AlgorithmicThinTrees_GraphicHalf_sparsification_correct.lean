-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_sparsification_correct
-- name    : OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:54.576489+00:00
-- url     : https://prove2.me/theorems/ef08fd0a-5ee1-420e-8068-e5b38cf716f1
-- title:
--   OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct` of [lean/OAI/Combinatorics/ThinTrees/Sparsification/Step.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/Step.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.GraphicHalf`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph`, `open MetricTests MetricTests.RationalStep Normalization RationalSigning`, `open scoped MatrixOrder`):
--
--   ```lean
--   theorem sparsification_correct : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
--       ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
--         (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
--         G.TreePackable (sparsify G r) (nextCount r) ∧
--         (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
--           (1/2+3*halfError r)*(G.cut univ S).card) ∧
--         (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrongThinTree.errorU` and `OAI.AlgorithmicThinTrees.GraphicHalf.halfError` (definitions bundle `OAIQ241TT001` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.nextCount` and `OAI.StrongThinTree.MultiGraph.TreePackable` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.sparsify` (definitions bundle `OAIQ241TT009` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.cut` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/Step.lean (declaration OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {d m : ℕ}

theorem sparsification_correct : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  sorry

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end
