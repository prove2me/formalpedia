-- Prove2me | Theorems.Thm_MetricGeometry_dist_lt_dist_of_comparisonAngle_lt
-- name    : MetricGeometry.dist_lt_dist_of_comparisonAngle_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:53:44.849869+00:00
-- url     : https://prove2.me/theorems/38c0019a-806e-4eca-b477-67276eb90706
-- title:
--   Strict monotonicity of the opposite side in the comparison angle
-- statement:
--   Let $p,x,y$ lie in one metric space and $q,u,v$ in another, with matched legs $d(p,x)=d(q,u)>0$ and
--   $d(p,y)=d(q,v)>0$. If the comparison angle at $p$ is *strictly* smaller than the comparison angle at $q$,
--   $\widetilde\angle_p(x,y)<\widetilde\angle_q(u,v)$, then the opposite sides are strictly ordered:
--
--   $$d(x,y)<d(u,v).$$
--
--   **Role.** This is the strict form of the monotonicity of the Euclidean chord in its opening angle. The
--   non-strict version suffices for most comparison estimates, but arguments that reach a contradiction from a
--   chain of inequalities need at least one link to be strict, and it is the angle comparison that supplies it.
--   In the proof that the Alexandrov angle satisfies the triangle inequality one builds a model configuration
--   whose apex angle is chosen *strictly* between two quantities; the strict inequality on angles is then traded
--   for a strict inequality on side lengths, and the resulting chain contradicts the triangle inequality of the
--   ambient space. The positivity hypotheses on the two legs are exactly what makes the trade strict: with a
--   degenerate leg the product of the legs vanishes and the comparison collapses to an equality.
--
--   The proof is again the law of cosines applied on both sides. With $a=d(q,u)>0$ and $b=d(q,v)>0$, the
--   difference of the squared opposite sides is $2ab\bigl(\cos\widetilde\angle_q(u,v)-\cos\widetilde\angle_p(x,y)\bigr)$;
--   comparison angles lie in $[0,\pi]$ where cosine is strictly decreasing, so the bracket is strictly negative,
--   and $2ab>0$ makes the whole expression strictly negative.
-- source:
--   The strict chord comparison used in the proof of Proposition I.1.14 (the triangle inequality for Alexandrov angles) in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), where it produces the three strict inequalities that contradict the triangle inequality in the ambient space.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem dist_lt_dist_of_comparisonAngle_lt {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (p x y : X) (q u v : Y)
    (hu : 0 < dist q u) (hv : 0 < dist q v)
    (h1 : dist p x = dist q u) (h2 : dist p y = dist q v)
    (hang : comparisonAngle p x y < comparisonAngle q u v) :
    dist x y < dist u v := by sorry

end MetricGeometry
