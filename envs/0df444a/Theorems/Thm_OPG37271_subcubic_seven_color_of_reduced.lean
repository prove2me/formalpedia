-- Prove2me | Theorems.Thm_OPG37271_subcubic_seven_color_of_reduced
-- name    : OPG37271.subcubic_seven_color_of_reduced
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-19T04:49:24.664194+00:00
-- url     : https://prove2.me/theorems/0604646a-7946-401b-a759-4fa32e0d8ba6
-- title:
--   Star 7-edge-coloring for reduced bridgeless subcubic simple graphs
-- statement:
--   Every finite bridgeless subcubic simple graph $G$ with no adjacent vertices of degree at most $2$ and no degree-$2$ vertex whose neighbors are adjacent admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Theorem 4.1(a).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem subcubic_seven_color_of_reduced {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsub : IsSubcubic G)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (hnoadj2 : ∀ u v : V, G.Adj u v → ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2))
    (hnotri2 : ∀ x y z : V, G.Adj x z → G.Adj y z → G.Adj x y → ¬ (G.neighborSet z).encard ≤ 2) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
