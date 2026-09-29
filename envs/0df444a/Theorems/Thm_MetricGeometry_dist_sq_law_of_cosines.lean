-- Prove2me | Theorems.Thm_MetricGeometry_dist_sq_law_of_cosines
-- name    : MetricGeometry.dist_sq_law_of_cosines
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T00:06:32.625489+00:00
-- url     : https://prove2.me/theorems/4e5778e0-851e-4eb6-9ba4-f49b0fafbc6f
-- title:
--   The law of cosines holds in every metric space
-- statement:
--   For any three points $p,x,y$ of a metric space,
--
--   $$
--   d(x,y)^2=d(p,x)^2+d(p,y)^2-2\,d(p,x)\,d(p,y)\cos\widetilde\angle_p(x,y).
--   $$
--
--   **Role.** The law of cosines is usually a theorem about Euclidean or inner product geometry. Read with the *comparison* angle in place of an actual angle, it holds verbatim in an arbitrary metric space, with no curvature hypothesis and no nondegeneracy hypothesis: it is the precise content of the assertion that every metric triangle has a Euclidean comparison triangle with the same side lengths.
--
--   Its practical use is to convert between the two ways of measuring how far apart two points on a sphere about $p$ are — the ambient distance, and the angle they subtend at $p$. Those are genuinely different quantities, the first a chord and the second an arc, and confusing them is the standard error in this subject. This identity is the exact exchange rate between them.
--
--   The degenerate cases are covered rather than excluded. If $d(p,x)=0$ then $d(x,y)=d(p,y)$ by the triangle inequality and both sides agree whatever the (then meaningless) angle happens to be.
-- source:
--   Standard comparison geometry: any triple of points of a metric space has a Euclidean comparison triangle. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, I.2.13 (the law of cosines in Euclidean space) and Lemma I.2.14 (existence of comparison triangles). Mathlib has the law of cosines for an inner product space but no comparison angle and no metric-space form.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem dist_sq_law_of_cosines {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    dist x y ^ 2 = dist p x ^ 2 + dist p y ^ 2
      - 2 * dist p x * dist p y * Real.cos (comparisonAngle p x y) := by sorry

end MetricGeometry
