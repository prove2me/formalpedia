-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_polynomial_nuclear_bound
-- name    : OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:56.317669+00:00
-- url     : https://prove2.me/theorems/83d0a6f6-da1a-4ce1-87a5-d064486c6c44
-- title:
--   OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound` of [lean/OAI/Combinatorics/ThinTrees/Metric/MatrixBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/MatrixBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricTests`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph`, `open scoped Classical MatrixOrder`):
--
--   ```lean
--   theorem polynomial_nuclear_bound :
--       ∃ qH : ℕ, 2 ≤ qH ∧ ∀ q : ℕ, qH ≤ q →
--         ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
--         H.LocallyConnectedReal G q →
--         ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
--         (∀t ∈ M, t ≠ univ) →
--         (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
--         ∀ (Z : Matrix (Fin n) (Fin n) ℝ), Test Z →
--         ∀ (lam : M → ℝ), (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
--         (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
--           (fun t : M => H.parentBoundary G t) lam*CFC.sqrt Z)).trace^2 ≤
--           ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrongThinTree.MultiGraph.incidence` and `OAI.StrongThinTree.MultiGraph.laplacian` (definitions bundle `OAIQ241TT001` of this split); `OAI.StrongThinTree.MultiGraph.Hierarchy`, `OAI.StrongThinTree.ShortcutDual.objectiveMatrix`, `OAI.StrongThinTree.MultiGraph.Hierarchy.LocallyConnectedReal` and `OAI.StrongThinTree.MultiGraph.Hierarchy.parentBoundary` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.MetricTests.Test` (definitions bundle `OAIQ241TT006` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.cut` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.Partitions.finite_chain_response` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/MatrixBound.lean (declaration OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

theorem polynomial_nuclear_bound :
    ∃ qH : ℕ, 2 ≤ qH ∧ ∀ q : ℕ, qH ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∀ (Z : Matrix (Fin n) (Fin n) ℝ), Test Z →
      ∀ (lam : M → ℝ), (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun t : M => H.parentBoundary G t) lam*CFC.sqrt Z)).trace^2 ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace := by
  sorry

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end
