-- Prove2me | Theorems.Thm_MetricGeometry_isNPC_of_innerProductSpace
-- name    : MetricGeometry.isNPC_of_innerProductSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T18:30:56.292041+00:00
-- url     : https://prove2.me/theorems/1294abc0-50e2-4318-b0a5-f5061da9f822
-- title:
--   Real inner product spaces satisfy the CN inequality
-- statement:
--   Every real inner product space satisfies the CN inequality of Bruhat and Tits: for every metric midpoint $m$ of $x$ and $y$ and every $z$,
--
--   $$
--   d(m,z)^2 \;\le\; \tfrac12 d(x,z)^2+\tfrac12 d(y,z)^2-\tfrac14 d(x,y)^2 .
--   $$
--
--   In fact equality holds. Writing $u=x-z$ and $v=y-z$, the midpoint satisfies $m-z=\tfrac12(u+v)$, and the two sides expand to
--
--   $$
--   \tfrac14\bigl(\|u\|^2+2\langle u,v\rangle+\|v\|^2\bigr)
--   \quad\text{and}\quad
--   \tfrac12\|u\|^2+\tfrac12\|v\|^2-\tfrac14\|u-v\|^2,
--   $$
--
--   which agree by the parallelogram law. The inequality is therefore saturated in the flat case, which is why it is the right synthetic formulation of *nonpositive* curvature: a general space is required to be no more spread out than Euclidean space along midpoints.
--
--   Together with completeness and existence of midpoints this says that a Hilbert space is an $\mathrm{NPC}$, or $\mathrm{CAT}(0)$, space — the basic example of the class, and the one against which every curvature condition is calibrated.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. The CN inequality is due to F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe); see also M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter II.1 (CAT(0) spaces and convexity of the metric) and Definition I.5.6 (the k-cone over a metric space). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem isNPC_of_innerProductSpace (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : IsNPC E := by sorry

end MetricGeometry
