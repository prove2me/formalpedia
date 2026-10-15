-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_eventually_line
-- name    : OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:14:09.887003+00:00
-- url     : https://prove2.me/theorems/58b6f008-12cd-4b31-a7c5-739d65be57d3
-- title:
--   Two-sided perturbations inside the degree and odd-cut polytope
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge has two distinct endpoints, and parallel edges are allowed and kept distinct. For $x\in\mathbb R^E$ and $v\in V$ let $d_x(v)=\sum_{e\ni v}x_e$ be the weighted degree of $v$ (the sum over the edges incident to $v$). For $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one endpoint in $S$, and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$. The *degree and odd-cut polytope* of $G$ is
--
--   $$
--   Q(G)=\Big\{x\in\mathbb R^E:\ x\ge0,\quad d_x(v)=1\ \text{for all } v\in V,\quad x(\delta(S))\ge1\ \text{for all } S\subseteq V\text{ with }|S|\text{ odd}\Big\}.
--   $$
--
--   Let $x\in Q(G)$ and let $u\in\mathbb R^E$ be a direction such that:
--
--   1. $u_e=0$ whenever $x_e=0$;
--   2. $d_u(v)=0$ for every vertex $v$;
--   3. $u(\delta(S))=0$ for every set $S\subseteq V$ of odd cardinality that is tight for $x$, i.e. $x(\delta(S))=1$.
--
--   Then there is $\eta>0$ such that
--
--   $$
--   x+t\,u\in Q(G)\qquad\text{for all real } t \text{ with } |t|<\eta .
--   $$
--
--   So a direction that respects the zero pattern of $x$, the degree equations and every tight odd cut can be followed in both directions while staying in $Q(G)$. It is used together with the extreme point criterion in the proof of Edmonds' perfect matching polytope theorem, and, through the face space of $x$, in the face-codimension bounds.
--
--   **Formalization Note** The conclusion is the filter statement `∀ᶠ t in 𝓝 0, x + t • u ∈ G.constraintPolytope`, which is equivalent to the existence of $\eta$. Finiteness of $V$ matters: only finitely many odd cuts have to be controlled.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean#L252-L290

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
theorem OAI.MatchingEntropy.LooplessGraph.constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by sorry
