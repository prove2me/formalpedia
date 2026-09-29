-- Prove2me | Theorems.Thm_MetricGeometry_dist_le_of_isLocalGeodesicWithSpeed
-- name    : MetricGeometry.dist_le_of_isLocalGeodesicWithSpeed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:01:09.942476+00:00
-- url     : https://prove2.me/theorems/f67268cb-8ee5-406b-95bb-40fbc87203cc
-- title:
--   A local geodesic of speed $k$ is globally $k$-Lipschitz
-- statement:
--   Let $c:\mathbb R\to X$ be a local geodesic of speed $k$ and scale $\delta>0$ in a metric space, so that
--
--   $$
--   d\bigl(c(s),c(t)\bigr)=k\,|s-t|\qquad\text{whenever }|s-t|\le\delta .
--   $$
--
--   Then the same relation holds as an inequality at *every* pair of parameters:
--
--   $$
--   d\bigl(c(s),c(t)\bigr)\le k\,|s-t|\qquad\text{for all }s,t\in\mathbb R .
--   $$
--
--   **Role.** A local geodesic is by definition only controlled at nearby parameters; over long parameter intervals it may wrap, self-intersect, or return, and then the distance between its endpoints is strictly less than the parameter separation times the speed. This theorem says that the local information nevertheless propagates to a global Lipschitz bound, obtained by chaining the defining identity along a chain of steps of size at most $\delta$ and applying the triangle inequality at each junction. Consequently $k\ge 0$ automatically, $c$ is continuous, and $c$ has locally bounded variation — which is what makes the length of a local geodesic well defined, and gives the upper half of the computation of that length.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 for geodesics, local geodesics and the length of a curve, and Proposition II.1.4(2) for local geodesics in CAT(0) spaces. Mathlib has `eVariationOn` but no notion of a local geodesic and no computation of the length of one.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem dist_le_of_isLocalGeodesicWithSpeed {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X) (k delta : ℝ) (h : IsLocalGeodesicWithSpeed c k delta) (s t : ℝ) :
    dist (c s) (c t) ≤ k * |s - t| := by sorry

end MetricGeometry
