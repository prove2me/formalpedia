-- Prove2me | Theorems.Thm_OPG37271_subcubic_ten_canonical_23
-- name    : OPG37271.subcubic_ten_canonical_23
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T07:38:27.378176+00:00
-- url     : https://prove2.me/theorems/1eaa7a85-2ffd-4e63-86d4-965a619cd1f1
-- title:
--   Star 7-Edge-Colorability on Fin 10 Over C₇+C₃ or C₆+C₄ Base Cycles
-- statement:
--   Every subcubic simple graph $G$ on $\mathrm{Fin}\,10$ containing the canonical $2$-regular cycle base (type `23`) admits a star $7$-edge-coloring.
-- source:
--   Finite 10-vertex certificate slice for Dvořák, Mohar, and Šámal (2013), Section 4.

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

theorem subcubic_ten_canonical_23 (G : SimpleGraph (Fin 10)) (hsub : IsSubcubic G)
    (hbase :
      (∀ p ∈ ([(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (7, 8), (7, 9), (8, 9)] : List (Fin 10 × Fin 10)), G.Adj p.1 p.2) ∨
      (∀ p ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5), (6, 7), (6, 9), (7, 8), (8, 9)] : List (Fin 10 × Fin 10)), G.Adj p.1 p.2)) :
    HasStarEdgeColoring G 7 := by sorry
end OPG37271
