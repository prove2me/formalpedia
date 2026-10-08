-- Prove2me | Theorems.Thm_MatousekLP_Integrality_vertex_cover_lp_rounding
-- name    : MatousekLP.Integrality.vertex_cover_lp_rounding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:29:10.463651+00:00
-- url     : https://prove2.me/theorems/7aac9cd4-3d26-4fdd-95e7-2f9f37b76af8
-- title:
--   §3.3 — LP rounding gives a vertex cover of at most twice the minimum size
-- statement:
--   Let $G = (V, E)$ be a finite graph (not necessarily bipartite), and let $x^*$ be an optimal solution of the LP relaxation (3.3),
--   $$
--   \text{minimize } \sum_{v \in V} x_v \quad \text{subject to } x_u + x_v \ge 1 \ (\{u,v\} \in E), \quad 0 \le x_v \le 1 \ (v \in V).
--   $$
--   Define $S_{LP} = \{ v \in V : x^*_v \ge \tfrac12 \}$ and let $S_{OPT}$ be a vertex cover of $G$ of the minimum possible size. Then $S_{LP}$ is a vertex cover of $G$, and
--   $$
--   |S_{LP}| \le 2 \cdot |S_{OPT}| .
--   $$
--
--   This is the analysis of the LP-rounding 2-approximation algorithm for minimum vertex cover.
--
--   **Formalization Note** Vertex covers are Mathlib's `SimpleGraph.IsVertexCover`; minimality of $S_{OPT}$ is the hypothesis that no vertex cover has fewer elements.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §3.3, p. 38, claim |S_LP| ≤ 2·|S_OPT| (LP relaxation (3.3): p. 37)

import Mathlib
import Definitions.Def_MatousekLP_Integrality_VertexCoverLP

namespace MatousekLP.Integrality

theorem vertex_cover_lp_rounding {V : Type*} [Fintype V] (G : SimpleGraph V)
    (xstar : V → ℝ) (hx : IsVCRelaxOptimal G xstar)
    (SOPT : Finset V) (hcov : G.IsVertexCover (SOPT : Set V))
    (hmin : ∀ C : Finset V, G.IsVertexCover (C : Set V) → SOPT.card ≤ C.card) :
    G.IsVertexCover {v | 1 / 2 ≤ xstar v} ∧
      (Finset.univ.filter (fun v => 1 / 2 ≤ xstar v)).card ≤ 2 * SOPT.card := by sorry

end MatousekLP.Integrality
