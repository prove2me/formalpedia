-- Prove2me | Theorems.Thm_OPG37271_k33_exact_six
-- name    : OPG37271.k33_exact_six
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T06:28:55.377125+00:00
-- url     : https://prove2.me/theorems/6c37cfaf-cffd-4714-ba83-abac80417b77
-- title:
--   The star chromatic index of $K_{3,3}$ is six
-- statement:
--   For the complete bipartite graph with two parts of three vertices, there exists a star edge coloring using six colors, and no star edge coloring using five colors exists. Equivalently,
--
--   $$
--   \chi'_s(K_{3,3})=6.
--   $$
--
--   Both assertions use proper edge colorings and prohibit bichromatic simple paths and cycles of four edges. This exact value shows that a universal six-color theorem for subcubic graphs would be sharp.
-- source:
--   Lei--Shi--Song, Star chromatic index of subcubic multigraphs, J. Graph Theory 88 (2018), 566--576, https://arxiv.org/abs/1701.04105v3, Section 1, paragraph following Theorem 1.3

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

/-- The complete bipartite graph K₃,₃ is star edge colorable with six colors
but not with five, showing that the conjectured six-color bound is sharp. -/
theorem k33_exact_six :
    HasStarEdgeColoring (completeBipartiteGraph (Fin 3) (Fin 3)) 6 ∧
    ¬ HasStarEdgeColoring (completeBipartiteGraph (Fin 3) (Fin 3)) 5 := by sorry

end OPG37271
