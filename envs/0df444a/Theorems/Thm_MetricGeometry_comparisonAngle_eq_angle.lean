-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_eq_angle
-- name    : MetricGeometry.comparisonAngle_eq_angle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:19:43.601591+00:00
-- url     : https://prove2.me/theorems/4ce41362-67c4-4125-a4a3-c804c48107c6
-- title:
--   In an inner product space the comparison angle is the angle
-- statement:
--   In a real inner product space the comparison angle is the actual angle: for points $p,x,y$,
--
--   $$
--   \widetilde\angle_p(x,y)=\angle(x-p,\;y-p).
--   $$
--
--   This is the law of cosines, in the form that justifies the name "comparison angle". Writing $u=x-p$ and $v=y-p$, the side lengths are $\|u\|$, $\|v\|$ and $\|u-v\|$, and expanding the last by the polarization identity,
--
--   $$
--   \|u-v\|^2=\|u\|^2-2\langle u,v\rangle+\|v\|^2 ,
--   $$
--
--   so the law-of-cosines quotient collapses:
--
--   $$
--   \frac{\|u\|^2+\|v\|^2-\|u-v\|^2}{2\|u\|\|v\|}
--   =\frac{2\langle u,v\rangle}{2\|u\|\|v\|}
--   =\frac{\langle u,v\rangle}{\|u\|\|v\|},
--   $$
--
--   which is exactly the argument of the arccosine defining the angle between $u$ and $v$. The cancellation of the factor $2$ is valid without any nondegeneracy hypothesis, so the identity holds at degenerate triangles too, both sides then being $\pi/2$ by the $0/0$ convention.
--
--   **Mathematical role.** Curvature bounds in the sense of Alexandrov are comparisons between the angles of a triangle and those of a Euclidean triangle with the same side lengths. This statement is the consistency check for that scheme: in the flat model the comparison angle is the angle, so a space of curvature bounded above by $0$ is one whose angles are no larger than the Euclidean ones.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_eq_angle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p x y : E) :
    comparisonAngle p x y = InnerProductGeometry.angle (x - p) (y - p) := by sorry

end MetricGeometry
