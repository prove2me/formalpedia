-- Prove2me | Theorems.Thm_OPG37271_root_problem
-- name    : OPG37271.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T06:29:09.16624+00:00
-- url     : https://prove2.me/theorems/8862f36b-473e-4801-a015-eaf26b4fb1c7
-- title:
--   OPG-37271: six colors for every finite subcubic graph
-- statement:
--   Let $G$ be any finite simple graph whose maximum degree is at most three. The problem asks for a star edge coloring of $G$ with six colors:
--
--   $$
--   \Delta(G)\le 3 \quad\Longrightarrow\quad \chi'_s(G)\le 6.
--   $$
--
--   The quantifier includes disconnected and empty graphs as well as graphs with vertices of degree below three. A star edge coloring is proper and forbids every bichromatic simple path or cycle of four edges; the paths need not be induced.
-- source:
--   Open Problem Garden, OPG-37271, https://www.openproblemgarden.org/comment/reply/37271; Conjecture 1.4 in Lei--Shi--Song, Star chromatic index of subcubic multigraphs, J. Graph Theory 88 (2018), 566--576, https://arxiv.org/abs/1701.04105v3

import Definitions.Def_opg37271_star_edge_coloring

namespace OPG37271

universe u

/-- OPG-37271: every finite simple graph of maximum degree at most three has
a star edge coloring with six colors. -/
theorem root_problem
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hsubcubic : IsSubcubic G) :
    HasStarEdgeColoring G 6 := by sorry

end OPG37271
