-- Prove2me | Theorems.Thm_OPG37271_subcubic_seven_color_of_no_adj_deg_le_two
-- name    : OPG37271.subcubic_seven_color_of_no_adj_deg_le_two
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-19T04:43:36.047272+00:00
-- url     : https://prove2.me/theorems/f7cd7c09-9bde-4061-bad1-aaafac4c5cf8
-- title:
--   Star 7-edge-coloring for bridgeless subcubic graphs with no adjacent vertices of degree ≤ 2
-- statement:
--   Every finite bridgeless subcubic simple graph $G$ in which no two vertices of degree at most $2$ are adjacent admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Theorem 4.1(a) reduced to bridgeless graphs with no adjacent degree-2 vertices.

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem subcubic_seven_color_of_no_adj_deg_le_two {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsub : IsSubcubic G)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (hnoadj2 : ∀ u v : V, G.Adj u v → ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2)) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
