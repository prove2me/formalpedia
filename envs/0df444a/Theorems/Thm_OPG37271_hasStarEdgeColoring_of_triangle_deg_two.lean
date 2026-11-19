-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_triangle_deg_two
-- name    : OPG37271.hasStarEdgeColoring_of_triangle_deg_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T04:49:24.92055+00:00
-- url     : https://prove2.me/theorems/bcd60e06-93d5-4de5-886e-6a7bf7fb74ed
-- title:
--   Reducibility of a degree-2 vertex in a triangle for star 7-edge-coloring
-- statement:
--   Let $G$ be a finite subcubic simple graph containing a triangle $xyz$ in which $z$ has degree at most $2$. If $G - xz$ admits a star $7$-edge-coloring, then $G$ also admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (degree-2 vertex with adjacent neighbors).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_triangle_deg_two {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (x y z : V)
    (hxz : G.Adj x z) (hyz : G.Adj y z) (hxy : G.Adj x y)
    (hz2 : (G.neighborSet z).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(x, z)}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
