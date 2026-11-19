-- Prove2me | Theorems.Thm_OPG37271_hasStarEdgeColoring_of_deg2_path4_distinct
-- name    : OPG37271.hasStarEdgeColoring_of_deg2_path4_distinct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T05:42:13.041305+00:00
-- url     : https://prove2.me/theorems/68620f06-432c-4872-9991-7cf5005e5e4f
-- title:
--   Reducibility of a 4-vertex path with degree-2 endpoints (distinct boundary)
-- statement:
--   Let $G$ be a finite subcubic simple graph containing a path $w - x - y - z$ where $\deg_G(w) \le 2$ and $\deg_G(z) \le 2$, and suppose the eight boundary vertices $w, x, y, z, w', x', y', z'$ (with $w w', x x', y y', z z' \in E(G)$) are pairwise distinct. If $G - \{wx, xy, yz\}$ admits a star $7$-edge-coloring, then $G$ also admits a star $7$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a) (Figure 2 / Cases 1–4).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem hasStarEdgeColoring_of_deg2_path4_distinct {V : Type u} [Fintype V]
    {G : SimpleGraph V} (hsub : IsSubcubic G) (w x y z w' x' y' z' : V)
    (hnd : [w, x, y, z, w', x', y', z'].Nodup)
    (hwx : G.Adj w x) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hww' : G.Adj w w') (hxx' : G.Adj x x') (hyy' : G.Adj y y') (hzz' : G.Adj z z')
    (hw2 : (G.neighborSet w).encard ≤ 2) (hz2 : (G.neighborSet z).encard ≤ 2)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(w, x), s(x, y), s(y, z)}) 7) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
