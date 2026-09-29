-- Prove2me | Theorems.Thm_OPG37271_subcubic_seven_color_bound
-- name    : OPG37271.subcubic_seven_color_bound
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T06:28:45.20441+00:00
-- url     : https://prove2.me/theorems/9eca08d9-e1ee-44bd-af2a-8b3a0927b19a
-- title:
--   The known seven-color bound for finite subcubic simple graphs
-- statement:
--   Let $G$ be a finite simple graph in which every vertex has at most three neighbors. Then $G$ admits a star edge coloring with seven colors:
--
--   $$
--   \Delta(G)\le 3 \quad\Longrightarrow\quad \chi'_s(G)\le 7.
--   $$
--
--   A star edge coloring is proper and has no bichromatic simple path or cycle of four edges. The path is not required to be induced. This is the established general upper bound that precedes the six-color conjecture.
-- source:
--   Dvořák--Mohar--Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313--326, https://arxiv.org/abs/1011.3376, subcubic seven-color theorem; restated as Theorem 1.3(a) in Lei--Shi--Song, Star chromatic index of subcubic multigraphs, J. Graph Theory 88 (2018), 566--576, https://arxiv.org/abs/1701.04105v3

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

universe u

/-- The known general upper bound: every finite subcubic simple graph has a
star edge coloring with seven colors. -/
theorem subcubic_seven_color_bound
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsubcubic : IsSubcubic G) :
    HasStarEdgeColoring G 7 := by sorry

end OPG37271
