-- Prove2me | Theorems.Thm_MetricGeometry_isGeodesicSegment_lineMap
-- name    : MetricGeometry.isGeodesicSegment_lineMap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:26:26.217375+00:00
-- url     : https://prove2.me/theorems/ba5dbc81-a347-4cb4-9c06-35974390a38f
-- title:
--   Straight lines in a normed space are geodesics
-- statement:
--   In a real normed space the straight line between two points is a geodesic: the map
--
--   $$
--   t\longmapsto (1-t)x+ty
--   $$
--
--   is a geodesic segment from $x$ to $y$ in the sense of an isometric parametrization of $[0,1]$ scaled by $d(x,y)$.
--
--   The verification is homogeneity of the norm. The difference of two parameter values is
--
--   $$
--   \bigl((1-s)x+sy\bigr)-\bigl((1-t)x+ty\bigr)=(t-s)(x-y),
--   $$
--
--   whose norm is $|t-s|\,\|x-y\|=|s-t|\,d(x,y)$, which is the defining identity.
--
--   **Why record it.** A geodesic segment is an axiomatic notion, and every statement quantifying over geodesics — uniqueness in nonpositive curvature, convexity of the metric along them, the straightness of the comparison angle at an interior point — is vacuous until examples exist. Normed spaces supply them, and they are the model case: a geodesic space is by design one in which every pair of points is joined by such a segment, with the normed situation as the flat prototype.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem isGeodesicSegment_lineMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) :
    IsGeodesicSegment (fun t : ℝ => (1 - t) • x + t • y) x y := by sorry

end MetricGeometry
