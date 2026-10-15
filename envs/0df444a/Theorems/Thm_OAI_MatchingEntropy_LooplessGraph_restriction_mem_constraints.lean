-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_restriction_mem_constraints
-- name    : OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:09:41.945857+00:00
-- url     : https://prove2.me/theorems/a40695b5-749b-47fd-9dcd-e5ef65789b3d
-- title:
--   Contracting the far side of a tight odd cut preserves the degree and odd-cut constraints
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge has two distinct endpoints, and parallel edges are allowed and kept distinct. For $x\in\mathbb R^E$ and $v\in V$ let $d_x(v)=\sum_{e\ni v}x_e$ be the weighted degree of $v$ (the sum over the edges incident to $v$). For $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one endpoint in $S$, and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$. The *degree and odd-cut polytope* of $G$ is
--
--   $$
--   Q(G)=\Big\{x\in\mathbb R^E:\ x\ge0,\quad d_x(v)=1\ \text{for all } v\in V,\quad x(\delta(S))\ge1\ \text{for all } S\subseteq V\text{ with }|S|\text{ odd}\Big\}.
--   $$
--
--   For $S\subseteq V$ let $G_S$ be the graph obtained from $G$ by deleting the edges with both endpoints outside $S$ and contracting $V\setminus S$ to a single new vertex $\ast$: its vertex set is $S\cup\{\ast\}$, its edges are the edges of $G$ with at least one endpoint in $S$ (keeping their identities), and an endpoint lying outside $S$ becomes $\ast$. In $G_S$ the edges at $\ast$ are exactly the edges of $\delta(S)$. For $x\in\mathbb R^E$ write $x|_S$ for the restriction of $x$ to the edges of $G_S$.
--
--   Let $x\in Q(G)$ and let $S\subseteq V$ be a set of odd cardinality that is tight for $x$, i.e. $x(\delta(S))=1$. Then
--
--   $$
--   x|_S\in Q(G_S).
--   $$
--
--   This is the reduction step for tight odd cuts in the inductive proof of Edmonds' perfect matching polytope theorem $Q(G)=\operatorname{conv}\{\mathbf 1_M\}$ for multigraphs, and in the induction bounding face codimensions. When $|V|$ is even, the complement $V\setminus S$ is also odd with the same cut, so $x$ splits into points of the constraint polytopes of the two smaller graphs $G_S$ and $G_{V\setminus S}$.
--
--   **Formalization Note** $G_S$ is `G.onSide S`, with vertex type `Option S`, where `none` is the contracted vertex $\ast$. The constraint polytope is `G.constraintPolytope`, and the odd-cut condition ranges over all finite vertex sets of odd cardinality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Contraction.lean#L401-L424

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

omit [DecidableEq E] in
theorem OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by sorry
