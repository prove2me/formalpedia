-- Prove2me | Theorems.Thm_OAI_Paper092_exists_step_to_boundary
-- name    : OAI.Paper092.exists_step_to_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:14:49.307177+00:00
-- url     : https://prove2.me/theorems/bfdcd2cb-e8b2-4ea2-9971-52e855bd89ed
-- title:
--   Moving along a ray from the nonnegative orthant until a decreasing coordinate vanishes
-- statement:
--   Let $\iota$ be a finite index set and let $q,v\in\mathbb{R}^\iota$ be real vectors such that $q_i\ge0$ for every $i\in\iota$ and $v_i<0$ for at least one $i\in\iota$. Then there is a step $t\ge0$ such that
--
--   $$q_j+t\,v_j\ge0\ \ \text{for all } j\in\iota,\qquad\text{and}\qquad q_i+t\,v_i=0\ \ \text{for some } i\in\iota\ \text{with } v_i<0 .$$
--
--   In words: moving from a point $q$ of the nonnegative orthant along the ray $q+tv$, $t\ge0$, one can stop at a point that is still in the orthant and at which some coordinate that strictly decreases along the ray has reached zero. Applied to the barycentric coordinates of a point of a simplex (or of a product of simplices) and to their velocities along a nonzero direction $u$, it shows that the ray from any point of the body in direction $u$ reaches a point of the body lying on a facet whose coordinate decreases along $u$. Consequently the orthogonal projection of the body onto $u^\perp$ is covered by the projections of these front facets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexProjection.lean#L48-L70

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection

open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped RealInnerProductSpace

theorem OAI.Paper092.exists_step_to_boundary {ι : Type uι} [Fintype ι] (q v : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hv : ∃ i, v i < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ i, 0 ≤ q i + t * v i) ∧
      ∃ i, v i < 0 ∧ q i + t * v i = 0 := by sorry
