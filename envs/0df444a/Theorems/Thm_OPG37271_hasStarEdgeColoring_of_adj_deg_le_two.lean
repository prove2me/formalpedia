-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_adj_deg_le_two
-- name    : OPG37271.hasStarEdgeColoring_of_adj_deg_le_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T04:43:37.314205+00:00
-- url     : https://prove2.me/theorems/96eff778-b9b2-4d3b-b44f-62abb23c1c07
-- title:
--   Reducibility of adjacent vertices of degree at most 2 in star 7-edge-coloring
-- statement:
--   Let $G$ be a finite subcubic simple graph containing an edge $e = uv$ whose endpoints both have degree at most $2$ in $G$. If $G - e$ admits a star $7$-edge-coloring, then $G$ also admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (adjacent degree-2 vertices reduction).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_adj_deg_le_two {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (u v : V) (huv : G.Adj u v)
    (hu2 : (G.neighborSet u).encard ≤ 2) (hv2 : (G.neighborSet v).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
