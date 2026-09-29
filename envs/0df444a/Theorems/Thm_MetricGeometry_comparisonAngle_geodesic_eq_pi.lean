-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_geodesic_eq_pi
-- name    : MetricGeometry.comparisonAngle_geodesic_eq_pi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:26:43.71052+00:00
-- url     : https://prove2.me/theorems/90623bb2-2859-4768-8031-e8f137e5f4cf
-- title:
--   The comparison angle at an interior point of a geodesic is $\pi$
-- statement:
--   At an interior point of a geodesic, the comparison angle subtended by the endpoints is straight: if $\gamma$ is a geodesic from $x$ to $y$ with $x\ne y$, and $0<t<1$, then
--
--   $$
--   \widetilde\angle_{\gamma(t)}(x,y)=\pi .
--   $$
--
--   Writing $D=d(x,y)>0$, the three side lengths are $d(\gamma(t),x)=tD$, $d(\gamma(t),y)=(1-t)D$ and $d(x,y)=D$, so the law-of-cosines quotient is
--
--   $$
--   \frac{t^2D^2+(1-t)^2D^2-D^2}{2\,tD\,(1-t)D}
--   =\frac{t^2+(1-t)^2-1}{2t(1-t)}
--   =\frac{-2t(1-t)}{2t(1-t)}=-1 ,
--   $$
--
--   and $\arccos(-1)=\pi$. The cancellation requires $t(1-t)D^2\ne0$, which is exactly the hypothesis that the point is interior and the endpoints distinct.
--
--   **Mathematical role.** Comparison angles are meant to measure how a triangle in a metric space differs from a Euclidean triangle with the same sides. This computation is the degenerate check: a triangle whose three vertices lie on one geodesic is flat, and the comparison angle at the middle vertex is straight, as it would be in the plane. It is also the reason the Alexandrov angle between the two halves of a geodesic is $\pi$, which is what makes a local geodesic locally length-minimizing and is the starting point of the billiards analysis in a spherical building, where paths are required to be straight except where they meet a wall.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_geodesic_eq_pi {X : Type*} [MetricSpace X]
    (g : ℝ → X) (x y : X) (h : IsGeodesicSegment g x y) (hxy : x ≠ y)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    comparisonAngle (g t) x y = Real.pi := by sorry

end MetricGeometry
