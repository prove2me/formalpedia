-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_degree_indicator
-- name    : OAI.MatchingEntropy.LooplessGraph.degree_indicator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:05:49.819041+00:00
-- url     : https://prove2.me/theorems/f78570f4-2f2f-4e23-92c0-0b42782afe35
-- title:
--   Indicator vectors of perfect matchings have every vertex degree equal to one
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$ (every edge has two distinct endpoints; parallel edges are allowed and kept distinct). For $x\in\mathbb R^E$ and $v\in V$ let
--
--   $$
--   d_x(v)=\sum_{e\in E:\ v\text{ is an endpoint of }e}x_e
--   $$
--
--   be the weighted degree of $v$. Let $M\subseteq E$ be a perfect matching of $G$, i.e. every vertex lies on exactly one edge of $M$, and let $\mathbf 1_M\in\mathbb R^E$ be its indicator vector. Then for every vertex $v\in V$,
--
--   $$
--   d_{\mathbf 1_M}(v)=\sum_{e\ni v}\mathbf 1_M(e)=1 .
--   $$
--
--   Thus every perfect matching vector satisfies the degree equations of the perfect matching polytope. Together with the odd-cut inequalities this gives the easy inclusion of Edmonds' perfect matching polytope theorem, namely that the convex hull of the perfect matching vectors lies in the polytope cut out by degree and odd-cut constraints.
--
--   **Formalization Note** The degree is `G.degree x v`, a sum over all edges of `if G.Incident v e then x e else 0`. The vertex type need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/OddCuts.lean#L56-L69

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
theorem OAI.MatchingEntropy.LooplessGraph.degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by sorry
