-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_30_twoVertexConnected
-- name    : NicerEars.TwoEC.theorem_30_twoVertexConnected
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T10:51:54.92526+00:00
-- url     : https://prove2.me/theorems/fe93e241-0561-4cef-ad44-f9f09848cab0
-- title:
--   Theorem 30, 2-vertex-connected case — a 2ECSS with at most 4/3 LP(G) edges
-- statement:
--   This is Theorem 30 of Sebő and Vygen in the case of 2-vertex-connected graphs, the case to which the proof of Theorem 30 reduces ("We may assume that our graph $G$ is 2-vertex-connected (Proposition 4)").
--
--   Let $G$ be a finite 2-vertex-connected graph, possibly with parallel edges but without loops. Then $G$ has a 2-edge-connected spanning subgraph $F\subseteq E(G)$ with
--
--   $$|F|\le\tfrac43\,\mathrm{LP}(G),\qquad \mathrm{LP}(G)=\min\Bigl\{x(E(G)) : x\in\mathbb R^{E(G)}_{\ge0},\ x(\delta(W))\ge2\ \text{for all}\ \emptyset\ne W\subsetneq V(G)\Bigr\}.$$
--
--   Together with the reduction to blocks (a 2-edge-connected graph with a cut vertex is the union of two smaller 2-edge-connected graphs sharing one vertex, and both $|F|$ and the LP bound add up over such a split), this yields Theorem 30 for all 2-edge-connected graphs.
--
--   **Formalization Note** "2-vertex-connected" is the platform predicate `Graph.IsTwoVertexConnected`: $G$ is 2-edge-connected and deleting any single vertex leaves a connected graph on the remaining vertices (this convention includes the one-vertex graph and two vertices joined by at least two parallel edges). As in the statement of Theorem 30 on the platform, "$|F|\le\frac43\mathrm{LP}(G)$" is stated as $|F|\le\frac43x(E(G))$ for every feasible point $x$ of $\mathrm{LP}(G)$, with $F$ chosen before $x$; $F$ uses each edge of $G$ at most once.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 22–23, Theorem 30 and its proof (first sentence: 'We may assume that our graph G is 2-vertex-connected (Proposition 4)')

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

theorem theorem_30_twoVertexConnected {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (hG : G.IsTwoVertexConnected) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by sorry

end NicerEars.TwoEC
