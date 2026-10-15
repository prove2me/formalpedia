-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_couple_laws
-- name    : OAI.MatchingEntropy.LooplessGraph.couple_laws
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:08:42.628493+00:00
-- url     : https://prove2.me/theorems/2a52cb4c-fcfc-47b9-8248-0a3ea11e6e47
-- title:
--   Gluing laws of perfect matchings on the two contracted sides of a cut
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$ (parallel edges allowed and kept distinct). A *perfect matching* of a graph is a set of edges covering every vertex exactly once; for a graph $K$ write $\mathcal M(K)$ for its set of perfect matchings, $\mathbf 1_M$ for the indicator vector of $M$, and for a probability vector (law) $p$ on $\mathcal M(K)$ let $\operatorname{mean}(p)=\sum_M p_M\mathbf 1_M$ be its vector of edge marginals. For $S\subseteq V$ let $G_S$ be the graph obtained from $G$ by deleting the edges with both endpoints outside $S$ and contracting $V\setminus S$ to a single new vertex $\ast$: its vertex set is $S\cup\{\ast\}$, its edges are the edges of $G$ with at least one endpoint in $S$ (keeping their identities), and an endpoint lying outside $S$ becomes $\ast$. In $G_S$ the edges at $\ast$ are exactly the edges of $\delta(S)$. Write $\bar S=V\setminus S$, so that $G_{\bar S}$ is obtained by contracting $S$ instead, and let $E_S$, $E_{\bar S}$ be the edge sets of $G_S$, $G_{\bar S}$.
--
--   Let $S\subseteq V$ and $x\in\mathbb R^E$. Let $p$ be a law on $\mathcal M(G_S)$ and $q$ a law on $\mathcal M(G_{\bar S})$ whose means agree with $x$:
--
--   $$
--   \operatorname{mean}(p)_e=x_e\ \ (e\in E_S),\qquad \operatorname{mean}(q)_e=x_e\ \ (e\in E_{\bar S}).
--   $$
--
--   Then there is a law $r$ on $\mathcal M(G)$ with $\operatorname{mean}(r)=x$; equivalently, $x$ lies in the perfect matching polytope $\operatorname{conv}\{\mathbf 1_M:M\in\mathcal M(G)\}$.
--
--   This is the gluing step for tight odd cuts. It is used in the induction proving Edmonds' perfect matching polytope theorem for multigraphs, and again in the bound on face codimensions: if the two contractions of $x$ along a tight odd cut lie in the perfect matching polytopes of the smaller graphs, then $x$ lies in the perfect matching polytope of $G$. No parity or tightness assumption on $S$ is needed in the statement; the existence of $p$ already forces $x(\delta(S))=1$, because every perfect matching of $G_S$ uses exactly one edge at $\ast$.
--
--   **Formalization Note** $G_S$ is `G.onSide S`, with vertex type `Option S` (the value `none` is the contracted vertex) and edge type the subtype of edges having an endpoint in $S$; $G_{\bar S}$ is `G.onSide Sᶜ`. The conclusion is `∃ r, r ∈ G.feasibleLaws x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Contraction.lean#L261-L299

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

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.LooplessGraph.couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by sorry
