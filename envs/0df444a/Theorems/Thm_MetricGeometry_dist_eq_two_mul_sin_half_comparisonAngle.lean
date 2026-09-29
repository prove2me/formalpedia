-- Prove2me | Theorems.Thm_MetricGeometry_dist_eq_two_mul_sin_half_comparisonAngle
-- name    : MetricGeometry.dist_eq_two_mul_sin_half_comparisonAngle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T00:06:47.642128+00:00
-- url     : https://prove2.me/theorems/34b71b7e-0c9c-49b6-9f01-c35fb628acf7
-- title:
--   Two points equidistant from $p$ are a chord apart
-- statement:
--   If $x$ and $y$ both lie at distance $L$ from $p$ in a metric space, then
--
--   $$
--   d(x,y)=2L\sin\frac{\widetilde\angle_p(x,y)}{2}.
--   $$
--
--   **Role.** This is the chord–arc dictionary on a metric sphere, in its sharpest form. On the sphere of radius $L$ about $p$, the ambient distance between two points is determined by, and determines, the angle they subtend at the centre — the two are related by the chord formula and by nothing simpler. In particular a curve on that sphere is parametrized at constant *angular* speed exactly when its ambient distances obey $d=2L|\sin(k\Delta/2)|$, which is strictly less than the arclength $kL|\Delta|$ at every nondegenerate pair.
--
--   For a homogeneous map into a metric cone whose unit circle lies at constant distance $L$ from the cone point, this is what makes the two natural formulations of the circle's behaviour interchangeable: the apartment chord law and the statement that the rescaled circle is a local geodesic of speed $\alpha$ in the space of directions. Each follows from the other by this identity alone.
--
--   Both halves of the range of the comparison angle are used: since $\widetilde\angle_p(x,y)\in[0,\pi]$, the half-angle lies in $[0,\pi/2]$ and its sine is nonnegative, so the square root of the law of cosines can be taken without an absolute value.
-- source:
--   Standard comparison geometry: any triple of points of a metric space has a Euclidean comparison triangle. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, I.2.13 (the law of cosines in Euclidean space) and Lemma I.2.14 (existence of comparison triangles). Mathlib has the law of cosines for an inner product space but no comparison angle and no metric-space form.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem dist_eq_two_mul_sin_half_comparisonAngle {X : Type*} [PseudoMetricSpace X]
    (p x y : X) (L : ℝ) (hx : dist p x = L) (hy : dist p y = L) :
    dist x y = 2 * L * Real.sin (comparisonAngle p x y / 2) := by sorry

end MetricGeometry
