-- Prove2me | Theorems.Thm_OPG37271_subcubic_ten_with_two_factor_hasStarEdgeColoring_seven
-- name    : OPG37271.subcubic_ten_with_two_factor_hasStarEdgeColoring_seven
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T07:13:57.294183+00:00
-- url     : https://prove2.me/theorems/72c53c3c-8476-4019-9403-7a8ce3fb418b
-- title:
--   Star 7-Edge-Colorability of 10-Vertex Subcubic Graphs with a 2-Factor
-- statement:
--   Every subcubic simple graph $G$ on $10$ vertices containing a $2$-regular spanning subgraph $T \le G$ (a $2$-factor, regardless of cycle partition $C_{10}$, $C_5 + C_5$, $C_7 + C_3$, $C_6 + C_4$, or $C_4 + C_3 + C_3$) admits a star $7$-edge-coloring.
-- source:
--   Base 10-vertex case for Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4.

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

theorem subcubic_ten_with_two_factor_hasStarEdgeColoring_seven
    (G T : SimpleGraph (Fin 10)) (hsub : IsSubcubic G) (hTG : T ≤ G)
    (h2reg : ∀ v : Fin 10, (T.neighborSet v).encard = 2) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
