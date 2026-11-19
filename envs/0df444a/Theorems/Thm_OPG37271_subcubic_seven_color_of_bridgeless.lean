-- Prove2me | Theorems.Thm_OPG37271_subcubic_seven_color_of_bridgeless
-- name    : OPG37271.subcubic_seven_color_of_bridgeless
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-19T04:39:27.330388+00:00
-- url     : https://prove2.me/theorems/dd82b18e-91ad-4e78-9f07-f28fc55280ea
-- title:
--   Star 7-edge-coloring for bridgeless finite subcubic simple graphs
-- statement:
--   Every finite bridgeless subcubic simple graph $G$ (where every edge lies on a cycle, i.e., removing any edge leaves its endpoints in the same connected component) admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, Theorem 4.1(a) reduced to the bridgeless case.

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem subcubic_seven_color_of_bridgeless {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsub : IsSubcubic G)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
