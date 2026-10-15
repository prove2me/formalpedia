-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_subset_polytope_aux
-- name    : OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:16:38.450982+00:00
-- url     : https://prove2.me/theorems/89a2b45e-7bae-4307-a867-9f5809de136e
-- title:
--   Edmonds' inclusion: the degree and odd-cut polytope lies inside the perfect matching polytope
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). For $x\in\mathbb{R}^E$, a vertex $v$ and a set $S\subseteq V$ write $\deg_x(v)=\sum_{e\ni v}x_e$ for the weighted degree and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$ for the cut mass, where $\delta(S)$ is the set of edges with exactly one endpoint in $S$. The degree and odd-cut polytope is
--
--   $$
--   Q(G)=\Bigl\{x\in\mathbb{R}^E:\ x_e\ge 0\ \text{for all } e,\ \ \deg_x(v)=1\ \text{for all } v,\ \ x(\delta(S))\ge 1\ \text{for all } S\subseteq V \text{ with } |S| \text{ odd}\Bigr\}.
--   $$
--
--   A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; its indicator vector is $\mathbf{1}_M\in\{0,1\}^E$. The perfect matching polytope $P(G)$ is the convex hull of these indicator vectors in $\mathbb{R}^E$.
--
--   **Theorem.** For every natural number $n$ and every such multigraph $G$ with $|V|=n$ and $n$ even,
--
--   $$
--   Q(G)\subseteq P(G).
--   $$
--
--   This is the substantial inclusion in Edmonds' perfect matching polytope theorem, here for multigraphs. Together with the elementary reverse inclusion (every perfect matching meets every odd cut) it gives $P(G)=Q(G)$ when $|V|$ is even, an explicit description of the perfect matching polytope by finitely many linear constraints. This description is what allows membership in $P(G)$ to be checked constraint by constraint in later local perturbation arguments.
--
--   **Formalization Note** The number of vertices $n$ is quantified first and the vertex and edge types afterwards, the shape needed for strong induction on $n$; the statement is equivalent to $Q(G)\subseteq P(G)$ for every finite loopless multigraph with an even number of vertices. If $G$ has no perfect matching then $P(G)$ is the convex hull of the empty set, and the theorem says that $Q(G)$ is empty too.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean#L344-L381

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

theorem OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by sorry
