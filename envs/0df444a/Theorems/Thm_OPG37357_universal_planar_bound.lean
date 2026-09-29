-- Prove2me | Theorems.Thm_OPG37357_universal_planar_bound
-- name    : OPG37357.universal_planar_bound
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-08T05:06:26.97545+00:00
-- url     : https://prove2.me/theorems/6db86006-37fd-4beb-87f6-84a3162e8153
-- title:
--   OPG-37357: a universal obstacle bound for planar graphs
-- statement:
--   There exists one natural number $k$ such that every finite simple planar graph has an ordinary obstacle drawing using at most $k$ polygonal obstacles:
--
--   $$
--   \exists k\in\mathbb N\ \forall n\in\mathbb N\ \forall G\text{ on }n\text{ vertices},
--   \qquad
--   G\text{ planar}\Longrightarrow\operatorname{obs}(G)\le k.
--   $$
--
--   The bound is chosen before the graph and is independent of graph order. The obstacle drawing need not be a crossing-free drawing of the graph.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-37357, https://www.unsolvedmath.com/problems/OPG-37357; historical conjectural bound discussed in Gimbel--Ossona de Mendez--Valtr, arXiv:1706.06992v3

import Definitions.Def_opg37357_obstacle_number

namespace OPG37357

/-- The still-open second part: a uniform finite obstacle bound for all finite
planar graphs. -/
theorem universal_planar_bound :
    ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      IsPlanar G → ObstacleNumberAtMost G k := by sorry

end OPG37357
