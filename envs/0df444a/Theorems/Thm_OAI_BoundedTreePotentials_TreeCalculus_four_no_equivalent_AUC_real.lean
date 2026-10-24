-- Prove2me | Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_no_equivalent_AUC_real
-- name    : OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:00.783475+00:00
-- url     : https://prove2.me/theorems/aa1bd503-5791-412e-b5cc-573d2715eb1b
-- title:
--   No space isomorphic to a tree-potential space is asymptotically uniformly convex (OpenAI bounded tree potentials, Theorem 2.1)
-- statement:
--   **The spaces** (all from the published bundle `Def_BoundedTreePotentials`). Nodes are finite lists of natural numbers (`Node`), and the potential of $f : \mathrm{Node} \to \mathbb R$ at a node $s$ is the sum of $f$ over the prefixes of $s$ (`potential`). For a flag $r$ (whether the root, the empty list, is a coordinate) and a quadratic kind $k$ (`QuadraticKind`: sibling, antichain or global), $f$ is a tree test (`IsTreeTest`) when it vanishes at the root if $r$ is false, every potential has absolute value at most $1$, $\sum_{s \in B} f(s)^2 \le 1$ for every admissible finite set $B$ of nodes (`QuadraticBudget`: children of one parent, pairwise prefix-incomparable, or arbitrary, according to $k$), and the support condition of $k$ holds (`CoefficientSupport`: none, finite support, square-summability). Finitely supported vectors $x$ on the coordinates get the norm $\sup_f |\sum_i x_i f_i|$ over tree tests $f$ (`treeTestFamily r k`, `testNorm`), and $X_{r,k}$ = `TestCompletion (treeTestFamily r k)` is the completion.
--
--   **Asymptotic uniform convexity.** For a real normed space $Y$, the one-sided modulus `oneSidedModulusReal Y t` is defined like the averaged one, with $\|y\| = 1$ in place of $\|y\| \ge 1$ and $\|x + ty\| - 1$ in place of the average; $Y$ is AUC (`IsAUCReal Y`) when this modulus is positive for every $t > 0$ (published bundle).
--
--   **The statement.** For every flag $r$, every quadratic kind $k$, and every real normed space $Y$ with a continuous linear equivalence $X_{r,k} \simeq Y$, the space $Y$ is not AUC:
--   $$\neg\,\texttt{IsAUCReal}\ Y.$$
--   So no equivalent norm on $X_{r,k}$ is asymptotically uniformly convex.
--
--   This is the third component of the goal `OAI.BoundedTreePotentials.TreeCalculus.main_counterexample`, from the paper's Theorem 2.1.
--
--   Lean: `OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real`, OpenAI's theorem of that name (in `lean/OAI/Analysis/TreePotential/EndpointTransfer.lean`).
-- source:
--   OpenAI, Midpoint convexity from bounded tree potentials and path costs, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 331; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf, Theorem 2.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TreePotential/EndpointTransfer.lean (declaration OAI.BoundedTreePotentials.TreeCalculus.four_no_equivalent_AUC_real)

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

namespace TreeCalculus

theorem four_no_equivalent_AUC_real (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬IsAUCReal Y := by
  sorry
end TreeCalculus

end BoundedTreePotentials

end

end OAI
end
