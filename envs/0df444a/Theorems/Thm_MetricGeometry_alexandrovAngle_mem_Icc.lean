-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_mem_Icc
-- name    : MetricGeometry.alexandrovAngle_mem_Icc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T22:51:34.717865+00:00
-- url     : https://prove2.me/theorems/b9852970-98fe-4c29-9287-9a547ed93612
-- title:
--   The Alexandrov angle lies in $[0,\pi]$
-- statement:
--   For any two curves $g_1,g_2$ issuing from a point $p$ of an arbitrary metric space,
--
--   $$
--   0\ \le\ \angle_p(g_1,g_2)\ \le\ \pi .
--   $$
--
--   **Role.** The Alexandrov angle is defined as a limit superior of comparison angles, and a limit superior of a bounded family need not inherit its bounds for free: one must know that the family is bounded above (so that the limit superior is not $+\infty$) and that the filter is nontrivial (so that it is not $-\infty$). Both hold here, the first because every comparison angle lies in $[0,\pi]$ and the second because a point of $\mathbb R$ is not isolated from the right. The conclusion is what makes the Alexandrov angle usable as an angle at all: it is the statement that the space of directions at a point, metrized by the upper angle, has diameter at most $\pi$, which is the first requirement for it to be a spherical space — and, in the case of a Euclidean building, a spherical building.
--
--   Note that no hypothesis whatsoever is placed on the curves or on the ambient space. The bound is a consequence of the range of $\arccos$ alone.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc

namespace MetricGeometry

theorem alexandrovAngle_mem_Icc {X : Type*} [PseudoMetricSpace X]
    (p : X) (g1 g2 : ℝ → X) :
    alexandrovAngle p g1 g2 ∈ Set.Icc 0 Real.pi := by sorry

end MetricGeometry
