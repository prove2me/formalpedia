-- Prove2me | Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_completed_space
-- name    : OAI.BoundedTreePotentials.TreeCalculus.four_completed_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:00.202925+00:00
-- url     : https://prove2.me/theorems/4e438198-1621-4d32-996f-98d1245aa402
-- title:
--   The four tree-potential spaces are separable infinite-dimensional Banach spaces (OpenAI bounded tree potentials, Theorem 2.1)
-- statement:
--   **The spaces** (all from the published bundle `Def_BoundedTreePotentials`). Nodes are finite lists of natural numbers (`Node`), and the potential of $f : \mathrm{Node} \to \mathbb R$ at a node $s$ is the sum of $f$ over the prefixes of $s$ (`potential`). For a flag $r$ (whether the root, the empty list, is a coordinate) and a quadratic kind $k$ (`QuadraticKind`: sibling, antichain or global), $f$ is a tree test (`IsTreeTest`) when it vanishes at the root if $r$ is false, every potential has absolute value at most $1$, $\sum_{s \in B} f(s)^2 \le 1$ for every admissible finite set $B$ of nodes (`QuadraticBudget`: children of one parent, pairwise prefix-incomparable, or arbitrary, according to $k$), and the support condition of $k$ holds (`CoefficientSupport`: none, finite support, square-summability). Finitely supported vectors $x$ on the coordinates get the norm $\sup_f |\sum_i x_i f_i|$ over tree tests $f$ (`treeTestFamily r k`, `testNorm`), and $X_{r,k}$ = `TestCompletion (treeTestFamily r k)` is the completion.
--
--   **The statement.** For every flag $r$ and every quadratic kind $k$, the space $X_{r,k}$ is complete, separable, and not finite-dimensional over $\mathbb R$.
--
--   This is the first component of the goal `OAI.BoundedTreePotentials.TreeCalculus.main_counterexample`, from the paper's Theorem 2.1.
--
--   Lean: `OAI.BoundedTreePotentials.TreeCalculus.four_completed_space`, OpenAI's theorem of that name (in `lean/OAI/Analysis/TreePotential/Normalization.lean`).
-- source:
--   OpenAI, Midpoint convexity from bounded tree potentials and path costs, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 331; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf, Theorem 2.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TreePotential/Normalization.lean (declaration OAI.BoundedTreePotentials.TreeCalculus.four_completed_space)

import Mathlib
import Definitions.Def_BoundedTreePotentials

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
open scoped Classical

namespace TreeCalculus
theorem four_completed_space (r : Bool) (k : QuadraticKind) :
    CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
    TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
    ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k)) := by
  sorry
end TreeCalculus
end BoundedTreePotentials

end

end OAI
end
