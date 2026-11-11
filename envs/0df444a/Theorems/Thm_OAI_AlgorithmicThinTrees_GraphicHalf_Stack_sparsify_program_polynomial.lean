-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_Stack_sparsify_program_polynomial
-- name    : OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:16.637208+00:00
-- url     : https://prove2.me/theorems/7d2faddf-cfea-4269-8386-01d4e3189f30
-- title:
--   OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial` of [lean/OAI/Combinatorics/ThinTrees/Sparsification/Realization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/Realization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.GraphicHalf.Stack`, with `open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset`, `open MetricTests MetricTests.RationalStep Normalization GraphStack`, `open MetricTests.RationalStep.Stack`):
--
--   ```lean
--   theorem sparsify_program_polynomial : ∃R : ℕ, 4 ≤ R ∧ ∀{ι : Type} {L : ι → ℕ}
--       (a : ι → Problem), IsPoly L (fun i => (problemCode (a i)).length) →
--       (∀i, R ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
--       RunsPoly L sparsifyProgram a
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Realization.boolCode` and `OAI.CurrentKS.Realization.listCode` (definitions bundle `OAIQ241TT000` of this split); `OAI.StrongThinTree.MultiGraph.TreePackable` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem` and `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemCode` (definitions bundle `OAIQ241TT005` of this split); `OAI.CurrentKS.Realization.IsPoly` and `OAI.CurrentKS.Realization.RunsPoly` (definitions bundle `OAIQ241TT006` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.sparsify` (definitions bundle `OAIQ241TT009` of this split); `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsifyProgram` (definitions bundle `OAIQ241TT014` of this split).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Sparsification/Realization.lean (declaration OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial)

import Mathlib
import Definitions.Def_OAIQ241TT014

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

theorem sparsify_program_polynomial : ∃R : ℕ, 4 ≤ R ∧ ∀{ι : Type} {L : ι → ℕ}
    (a : ι → Problem), IsPoly L (fun i => (problemCode (a i)).length) →
    (∀i, R ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
    RunsPoly L sparsifyProgram a := by
  sorry

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end
