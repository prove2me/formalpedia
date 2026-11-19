-- Prove2me | Theorems.Thm_OPG37271_cycle_ne_five_hasStarEdgeColoring_three
-- name    : OPG37271.cycle_ne_five_hasStarEdgeColoring_three
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T05:21:15.544848+00:00
-- url     : https://prove2.me/theorems/03b49956-7542-405c-b54f-a1172e93d248
-- title:
--   Every cycle of length n ≠ 5 admits a star 3-edge-coloring
-- statement:
--   For every integer $n \ge 3$ with $n \ne 5$, the $n$-vertex cycle graph $C_n$ admits a star $3$-edge-coloring.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Section 4, proof of Theorem 4.1(a).

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

theorem cycle_ne_five_hasStarEdgeColoring_three (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≠ 5) :
    HasStarEdgeColoring (SimpleGraph.fromRel (fun i j : Fin n => (i.val + 1) % n = j.val)) 3 := by sorry
end OPG37271
