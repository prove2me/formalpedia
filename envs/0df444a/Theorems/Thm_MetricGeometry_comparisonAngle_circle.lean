-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_circle
-- name    : MetricGeometry.comparisonAngle_circle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:21:28.693479+00:00
-- url     : https://prove2.me/theorems/8874019b-46a1-479b-991c-2dbfeb21f24b
-- title:
--   The comparison angle at the centre of a Euclidean circle is the angular difference
-- statement:
--   Let $v_1,v_2$ be an orthonormal pair in a real inner product space, $L>0$, and consider the circle of radius $L$ about a point $p$ in the plane they span,
--
--   $$
--   c(s)=p+L\bigl(\cos(s)\,v_1+\sin(s)\,v_2\bigr).
--   $$
--
--   Then for $|s-t|\le\pi$ the comparison angle at the centre subtended by two points of the circle is exactly the difference of their parameters:
--
--   $$
--   \widetilde\angle_p\bigl(c(s),c(t)\bigr)=|s-t| .
--   $$
--
--   **Role.** This is the model computation that separates the *chord* from the *arc*. The distance between $c(s)$ and $c(t)$ is the chord $2L\lvert\sin\frac{s-t}{2}\rvert$, which is strictly smaller than the arclength $L|s-t|$ whenever the two points are distinct; it is the *angle* at the centre, not the distance, that reproduces the parameter difference. Any statement asserting that a circular arc is traversed at constant speed must therefore be made for the angular metric — the metric of the space of directions at the centre — and not for the ambient metric.
--
--   That distinction is exactly the one at work for a homogeneous map into a conical building whose unit circle has constant distance $L$ from the cone point: locally the image lies in an apartment as a circle of radius $L$ about the cone point, traversed at angular rate $\alpha$, so the comparison angle at the cone point grows at unit rate in the arclength parameter while the ambient distance does not.
--
--   The hypothesis $|s-t|\le\pi$ is necessary: beyond half a turn the comparison angle stops growing and starts to decrease, since the angle between two vectors never exceeds $\pi$.
-- source:
--   Elementary Euclidean geometry (the inscribed circle and the law of cosines). The role it plays is that of the apartment computation in the proof of Lemma 4.2 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_metric_geodesic_angle
import Definitions.Def_spherical_great_circle

namespace MetricGeometry

theorem comparisonAngle_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p v1 v2 : E) (L : ℝ) (hL : 0 < L)
    (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (s t : ℝ) (hst : |s - t| ≤ Real.pi) :
    comparisonAngle p (p + L • SphericalGeometry.greatCirclePath v1 v2 s)
        (p + L • SphericalGeometry.greatCirclePath v1 v2 t)
      = |s - t| := by sorry

end MetricGeometry
