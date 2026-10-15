-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_mem_polytope_iff
-- name    : OAI.MatchingEntropy.LooplessGraph.mem_polytope_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:57:59.354588+00:00
-- url     : https://prove2.me/theorems/cac8517c-3f5e-4843-a0fe-089e184b9248
-- title:
--   A vector lies in the perfect matching polytope iff it is the mean of a probability law on perfect matchings
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; $\mathcal M(G)$ denotes the finite set of perfect matchings and $\mathbf 1_M\in\{0,1\}^E$ the indicator vector of $M$. The perfect matching polytope of $G$ is the convex hull
--   $$
--   P(G)=\operatorname{conv}\{\mathbf 1_M: M\in\mathcal M(G)\}\subseteq\mathbb{R}^E .
--   $$
--   A *feasible law* for $y\in\mathbb{R}^E$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$, with $p_M\ge0$ and $\sum_M p_M=1$, whose mean is $y$, i.e. $\sum_M p_M\,\mathbf 1_M(e)=y_e$ for every $e\in E$.
--
--   **Theorem.** For every $y\in\mathbb{R}^E$,
--   $$
--   y\in P(G)\quad\Longleftrightarrow\quad\text{there exists a feasible law for }y .
--   $$
--
--   Equivalently, $P(G)$ is exactly the set of edge marginals $e\mapsto\Pr[e\in\mathbf M]$ of random perfect matchings $\mathbf M$. This lets one pass between the geometric and the probabilistic descriptions of the polytope. In particular, the maximal entropy $\sup\{H(p): p\text{ feasible for }y\}$ is a supremum over a nonempty set precisely when $y\in P(G)$.
--
--   **Formalization Note** The right-hand side is `(G.feasibleLaws y).Nonempty`. In this statement the vertex type is not required to be finite. If $G$ has no perfect matching, both sides are false: the convex hull of the empty set is empty, and there is no probability vector on an empty index set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Basic.lean#L82-L97

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem OAI.MatchingEntropy.LooplessGraph.mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by sorry
