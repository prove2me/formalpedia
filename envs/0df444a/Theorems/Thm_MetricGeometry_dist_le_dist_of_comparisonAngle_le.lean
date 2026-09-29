-- Prove2me | Theorems.Thm_MetricGeometry_dist_le_dist_of_comparisonAngle_le
-- name    : MetricGeometry.dist_le_dist_of_comparisonAngle_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:43:45.74363+00:00
-- url     : https://prove2.me/theorems/a8958a46-66e0-4056-b782-4632a5965cc7
-- title:
--   The opposite side is monotone in the comparison angle
-- statement:
--   Let $p,x,y$ be points of one metric space and $q,u,v$ points of another, with the two legs matched:
--   $d(p,x)=d(q,u)$ and $d(p,y)=d(q,v)$. If the comparison angle at $p$ is at most the comparison angle at $q$,
--   $\widetilde\angle_p(x,y)\le\widetilde\angle_q(u,v)$, then the opposite sides are ordered the same way:
--   $d(x,y)\le d(u,v)$.
--
--   **Role.** This is the monotonicity of the Euclidean chord in its opening angle, transported to metric spaces
--   through the comparison angle. It converts a hypothesis about angles into a hypothesis about distances, which
--   is the only form the triangle inequality of the ambient space can consume. In the proof that the Alexandrov
--   angle satisfies the triangle inequality, one builds a Euclidean model triangle whose angle at the apex is
--   squeezed between two quantities; each squeeze is then cashed in for a comparison of side lengths, once in
--   each direction, and the two comparisons are combined with the triangle inequality in $X$ to reach a
--   contradiction. This statement is exactly that exchange step.
--
--   The proof is the law of cosines twice. Writing $a=d(q,u)$, $b=d(q,v)$, and using
--   $d(x,y)^2=a^2+b^2-2ab\cos\widetilde\angle_p(x,y)$ together with the corresponding identity for $d(u,v)$,
--   the difference of squares is $2ab\,(\cos\widetilde\angle_q(u,v)-\cos\widetilde\angle_p(x,y))$. Comparison angles
--   lie in $[0,\pi]$, where cosine is decreasing, so the assumed inequality on angles reverses to
--   $\cos\widetilde\angle_q(u,v)\le\cos\widetilde\angle_p(x,y)$, making the difference of squares nonpositive; both
--   distances are nonnegative, so the inequality passes from squares to the distances themselves.
--
--   Note that the two triples need not lie in the same space, and no geodesics, no completeness, and no curvature
--   bound are involved — only six points and their mutual distances.
-- source:
--   The monotonicity of the Euclidean chord length in its opening angle, used twice in the proof of Proposition I.1.14 (the triangle inequality for Alexandrov angles) in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles).

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem dist_le_dist_of_comparisonAngle_le {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (p x y : X) (q u v : Y)
    (h1 : dist p x = dist q u) (h2 : dist p y = dist q v)
    (hang : comparisonAngle p x y ≤ comparisonAngle q u v) :
    dist x y ≤ dist u v := by sorry

end MetricGeometry
