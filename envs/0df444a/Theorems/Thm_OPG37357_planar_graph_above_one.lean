-- Prove2me | Theorems.Thm_OPG37357_planar_graph_above_one
-- name    : OPG37357.planar_graph_above_one
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-08T05:06:12.569381+00:00
-- url     : https://prove2.me/theorems/93bbb90f-b40d-4041-bf80-ba3fb3cf2191
-- title:
--   A finite planar graph of obstacle number two
-- statement:
--   There exists a finite simple planar graph $G$ whose ordinary obstacle number is exactly two in the mission's polygonal model:
--
--   $$
--   \operatorname{obs}(G)\le2
--   \qquad\text{and}\qquad
--   \operatorname{obs}(G)\not\le1.
--   $$
--
--   This is the published positive answer to the first part of OPG-37357. The existential statement permits formalization using any of the planar examples proved in the cited paper.
-- source:
--   Berman--Chappell--Faudree--Gimbel--Hartman--Williams, Graphs with Obstacle Number Greater than One, JGAA 21(6) (2017), Proposition 3, p. 1113, https://doi.org/10.7155/jgaa.00452

import Definitions.Def_opg37357_obstacle_number

namespace OPG37357

/-- Published positive answer to the first part: some finite planar graph has
ordinary obstacle number exactly two. -/
theorem planar_graph_above_one :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      IsPlanar G ∧ ObstacleNumberAtMost G 2 ∧ ¬ ObstacleNumberAtMost G 1 := by sorry

end OPG37357
