-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_supportSimple_has_perfectMatching
-- name    : OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:12:54.329189+00:00
-- url     : https://prove2.me/theorems/cba13f7b-a25a-4e94-81e9-fa5a5336be42
-- title:
--   The support graph of a point of the degree and odd-cut polytope has a perfect matching
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge has two distinct endpoints, and parallel edges are allowed and kept distinct. For $x\in\mathbb R^E$ and $v\in V$ let $d_x(v)=\sum_{e\ni v}x_e$ be the weighted degree of $v$ (the sum over the edges incident to $v$). For $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one endpoint in $S$, and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$. The *degree and odd-cut polytope* of $G$ is
--
--   $$
--   Q(G)=\Big\{x\in\mathbb R^E:\ x\ge0,\quad d_x(v)=1\ \text{for all } v\in V,\quad x(\delta(S))\ge1\ \text{for all } S\subseteq V\text{ with }|S|\text{ odd}\Big\}.
--   $$
--
--   For $x\in\mathbb R^E$ the *support graph* $G_x$ is the simple graph on $V$ in which two vertices $v\neq w$ are adjacent if and only if some edge $e$ with $x_e>0$ has endpoints $v$ and $w$.
--
--   If $x\in Q(G)$, then $G_x$ has a perfect matching:
--
--   $$
--   \exists\,M\subseteq E(G_x)\ \text{ such that every } v\in V \text{ lies on exactly one edge of } M .
--   $$
--
--   Choosing for each edge of such an $M$ a supporting edge of $G$ of positive weight gives a perfect matching of $G$ inside the support of $x$. This is the first step in the proof of Edmonds' perfect matching polytope theorem: at an extreme point $x$ of $Q(G)$ without nontrivial tight odd cuts, the direction from $x$ to such a matching vector is admissible in both directions, which forces $x$ to be that matching vector.
--
--   **Formalization Note** The support graph is `G.supportSimple x`, a Mathlib `SimpleGraph V`, and the conclusion is `∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching`, a spanning subgraph in which every vertex has degree one. Passing to the simple support graph forgets only the identities of parallel edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean#L137-L191

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem OAI.MatchingEntropy.LooplessGraph.supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by sorry
