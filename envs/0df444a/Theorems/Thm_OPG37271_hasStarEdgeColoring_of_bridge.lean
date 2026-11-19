-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_bridge
-- name    : OPG37271.hasStarEdgeColoring_of_bridge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T04:39:27.3332+00:00
-- url     : https://prove2.me/theorems/0e5e9592-9775-41d2-a6a1-49a35d910abb
-- title:
--   Bridge reduction for star 7-edge-coloring of subcubic graphs
-- statement:
--   Let $G$ be a finite subcubic simple graph and let $e = uv$ be a bridge (cut-edge) of $G$. If $G - e$ admits a star $7$-edge-coloring, then $G$ also admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (2-connectivity step).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_bridge {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (u v : V) (huv : G.Adj u v)
    (hbridge : ¬ (G.deleteEdges {s(u, v)}).Reachable u v)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
