-- Prove2me | Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_averaged_modulus_real
-- name    : OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:03.53552+00:00
-- url     : https://prove2.me/theorems/6e4d6328-3fb4-4776-9f7a-b8c611a727dd
-- title:
--   The tree-potential spaces have averaged midpoint modulus at least √(1 + t²/4) − 1 (OpenAI bounded tree potentials, Theorem 2.1)
-- statement:
--   **The spaces** (all from the published bundle `Def_BoundedTreePotentials`). Nodes are finite lists of natural numbers (`Node`), and the potential of $f : \mathrm{Node} \to \mathbb R$ at a node $s$ is the sum of $f$ over the prefixes of $s$ (`potential`). For a flag $r$ (whether the root, the empty list, is a coordinate) and a quadratic kind $k$ (`QuadraticKind`: sibling, antichain or global), $f$ is a tree test (`IsTreeTest`) when it vanishes at the root if $r$ is false, every potential has absolute value at most $1$, $\sum_{s \in B} f(s)^2 \le 1$ for every admissible finite set $B$ of nodes (`QuadraticBudget`: children of one parent, pairwise prefix-incomparable, or arbitrary, according to $k$), and the support condition of $k$ holds (`CoefficientSupport`: none, finite support, square-summability). Finitely supported vectors $x$ on the coordinates get the norm $\sup_f |\sum_i x_i f_i|$ over tree tests $f$ (`treeTestFamily r k`, `testNorm`), and $X_{r,k}$ = `TestCompletion (treeTestFamily r k)` is the completion.
--
--   **The modulus.** For a real normed space $E$ and $t$, `averagedModulusReal E t` is the infimum over unit vectors $x$ of the supremum over closed finite-codimensional subspaces $F$ (`ClosedFiniteCodim`) of the infimum over $y \in F$ with $\|y\| \ge 1$ of $\tfrac12(\|x + ty\| + \|x - ty\|) - 1$. The infima and suprema are taken in $\mathbb R$ with Mathlib's conventions (an empty or unbounded family gives $0$).
--
--   **The statement.** For every flag $r$, every quadratic kind $k$ and every $0 < t < 1$,
--   $$\sqrt{1 + t^2/4} - 1 \;\le\; \texttt{averagedModulusReal}\ X_{r,k}\ t.$$
--
--   This is the second component of the goal `OAI.BoundedTreePotentials.TreeCalculus.main_counterexample`, from the paper's Theorem 2.1.
--
--   Lean: `OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real`, OpenAI's theorem of that name (in `lean/OAI/Analysis/TreePotential/EndpointTransfer.lean`).
-- source:
--   OpenAI, Midpoint convexity from bounded tree potentials and path costs, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 331; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf, Theorem 2.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TreePotential/EndpointTransfer.lean (declaration OAI.BoundedTreePotentials.TreeCalculus.four_averaged_modulus_real)

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

theorem four_averaged_modulus_real (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    Real.sqrt (1+t^2/4)-1≤ averagedModulusReal (TestCompletion (treeTestFamily r k)) t := by
  sorry

end TreeCalculus

end BoundedTreePotentials

end

end OAI
end
