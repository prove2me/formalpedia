-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_faceSpace_of_side_spaces
-- name    : OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:17:20.995744+00:00
-- url     : https://prove2.me/theorems/69b81089-2f27-473d-b677-356fb091cbf8
-- title:
--   Face directions glue across a tight odd cut
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Assume that $|V|$ is even. For $x\in\mathbb{R}^E$, a vertex $v$ and a set $S\subseteq V$ write $\deg_x(v)=\sum_{e\ni v}x_e$ for the weighted degree and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$ for the cut mass, where $\delta(S)$ is the set of edges with exactly one endpoint in $S$. The degree and odd-cut polytope is
--
--   $$
--   Q(G)=\Bigl\{x\in\mathbb{R}^E:\ x_e\ge 0\ \text{for all } e,\ \ \deg_x(v)=1\ \text{for all } v,\ \ x(\delta(S))\ge 1\ \text{for all } S\subseteq V \text{ with } |S| \text{ odd}\Bigr\}.
--   $$
--
--   Fix $x\in Q(G)$. Let $E_+=\{e\in E: x_e>0\}$ be the positive support of $x$, and for $u\in\mathbb{R}^{E_+}$ let $\tilde u\in\mathbb{R}^E$ be its extension by zero. The active face space of $x$ is the linear subspace
--
--   $$
--   \mathcal{F}(G,x)=\Bigl\{u\in\mathbb{R}^{E_+}:\ \deg_{\tilde u}(v)=0\ \text{for all } v\in V,\ \ \tilde u(\delta(T))=0\ \text{for every odd } T\subseteq V \text{ with } x(\delta(T))=1\Bigr\},
--   $$
--
--   the directions supported on $E_+$ that keep every active (tight) constraint of $Q(G)$ at $x$.
--
--   For a set $S\subseteq V$, the contraction $G_S$ is the multigraph obtained by shrinking $V\setminus S$ to one new vertex $\ast$: its vertex set is $S\cup\{\ast\}$, its edge set $E_S$ consists of the edges of $G$ with at least one endpoint in $S$ (keeping their identities), and an endpoint outside $S$ is replaced by $\ast$. Write $x_S$ for the restriction of $x$ to $E_S$; its positive support is $E_+\cap E_S$, and $u|_S$ denotes the restriction of $u\in\mathbb{R}^{E_+}$ to $E_+\cap E_S$. The same notation is used for the complement $S^c=V\setminus S$.
--
--   **Theorem.** Let $S\subseteq V$ be a set of odd size whose cut is tight, $x(\delta(S))=1$. If $u\in\mathbb{R}^{E_+}$ satisfies
--
--   $$
--   u|_S\in\mathcal{F}(G_S,x_S)\qquad\text{and}\qquad u|_{S^c}\in\mathcal{F}(G_{S^c},x_{S^c}),
--   $$
--
--   then $u\in\mathcal{F}(G,x)$.
--
--   The content is that the active constraints of $G$ at $x$ are controlled by those of the two contractions, including the constraints for odd sets $T$ that cross $S$ and are invisible to either side alone. In linear-algebra terms, the kernel of the map $u\mapsto\bigl(u|_S+\mathcal{F}(G_S,x_S),\ u|_{S^c}+\mathcal{F}(G_{S^c},x_{S^c})\bigr)$ into the product of the two quotient spaces is contained in $\mathcal{F}(G,x)$, so by rank–nullity the face codimension $\dim\bigl(\mathbb{R}^{E_+}/\mathcal{F}(G,x)\bigr)$ is at most the sum of the face codimensions of $x_S$ and $x_{S^c}$ in the contractions; this is the step that drives the induction bounding face codimensions.
--
--   **Formalization Note** The contraction $G_S$ is `G.onSide S`, with vertex type `Option S` (the value `none` is the contracted vertex) and edge type the subtype of edges having an endpoint in $S$; $x_S$ and $u|_S$ are `G.sideMarginal x S` and `G.sideRestriction x S u`. The set $S$ need not be nontrivial: $|S|=1$ is allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Face.lean#L149-L178

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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.LooplessGraph.faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by sorry
