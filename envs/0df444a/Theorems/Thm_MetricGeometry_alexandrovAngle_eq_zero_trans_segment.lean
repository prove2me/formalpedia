-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_eq_zero_trans_segment
-- name    : MetricGeometry.alexandrovAngle_eq_zero_trans_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:09:50.651187+00:00
-- url     : https://prove2.me/theorems/403c227b-02dc-48ca-b8aa-f89deb389cc8
-- title:
--   Defining the same direction is transitive for geodesic segments
-- statement:
--   Let $g,g',g''$ be nondegenerate geodesic segments issuing from a common point $p$. If $g$ and $g'$ define the
--   same direction, and $g'$ and $g''$ do, then so do $g$ and $g''$:
--
--   $$\angle(g,g')=0\ \text{and}\ \angle(g',g'')=0\ \Longrightarrow\ \angle(g,g'')=0 .$$
--
--   **Role.** This completes the verification that "defining the same direction at $p$" is an equivalence relation
--   on the nondegenerate geodesic segments issuing from $p$. Reflexivity is the vanishing of the angle of a
--   segment with itself and symmetry is the symmetry of the angle; transitivity is the only one of the three that
--   needs the triangle inequality, and hence the only one that is a theorem rather than a computation.
--
--   With all three in hand, the set of geodesic segments $[p,y]$ with $y\neq p$ carries a genuine equivalence
--   relation, the Alexandrov angle is a pseudometric on it, and the quotient — the space of directions
--   $\Sigma_pX$ — is a metric space. That object is the local model at $p$ for spaces of curvature bounded above:
--   in a Euclidean building it carries a spherical building structure, and its geometry is what controls the local
--   behaviour of maps into the building.
--
--   **The argument.** Apply the triangle inequality for angles between geodesic segments with $g'$ in the reference
--   role: $\angle(g,g'')\le\angle(g',g)+\angle(g',g'')$. By symmetry $\angle(g',g)=\angle(g,g')=0$, and
--   $\angle(g',g'')=0$ by hypothesis, so $\angle(g,g'')\le0$. Angles are nonnegative, so it vanishes.
-- source:
--   The consequence of Proposition I.1.14 recorded in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1: the triangle inequality for angles implies that the relation given by vanishing of the Alexandrov angle is an equivalence relation on the geodesics issuing from a point; stated here for segments normalized on the unit interval.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_eq_zero_trans_segment {X : Type*} [PseudoMetricSpace X]
    (p y y' y'' : X) (g g' g'' : ℝ → X)
    (hg : IsGeodesicSegment g p y) (hg' : IsGeodesicSegment g' p y')
    (hg'' : IsGeodesicSegment g'' p y'')
    (hy : dist p y ≠ 0) (hy' : dist p y' ≠ 0) (hy'' : dist p y'' ≠ 0)
    (h1 : alexandrovAngle p g g' = 0) (h2 : alexandrovAngle p g' g'' = 0) :
    alexandrovAngle p g g'' = 0 := by sorry

end MetricGeometry
