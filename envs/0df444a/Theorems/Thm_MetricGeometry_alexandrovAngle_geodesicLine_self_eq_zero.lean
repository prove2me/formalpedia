-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_geodesicLine_self_eq_zero
-- name    : MetricGeometry.alexandrovAngle_geodesicLine_self_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T22:52:01.145584+00:00
-- url     : https://prove2.me/theorems/3d0433d9-f213-4384-a854-16f2f9094433
-- title:
--   A geodesic makes angle zero with itself
-- statement:
--   Let $\gamma:\mathbb R\to X$ be a geodesic line in a metric space. Then
--
--   $$
--   \angle_{\gamma(0)}(\gamma,\gamma)=0 .
--   $$
--
--   **Role.** The Alexandrov angle is intended to be a *pseudometric* on the set of geodesics issuing from a point, whose quotient is the space of directions. Vanishing on the diagonal is the first of the pseudometric axioms, and it is not automatic from the definition: the angle is a limit superior of comparison angles taken at two *independent* parameters $s,t\to0^+$, so even for a single curve the quantity being bounded is $\widetilde\angle_p(\gamma(s),\gamma(t))$ with $s\ne t$, and it vanishes only because $d(\gamma(s),\gamma(t))=|s-t|$ makes the comparison triangle degenerate to a segment for every such pair. For a merely continuous curve the self-angle can be positive; it is exactly the geodesic condition that collapses it.
--
--   With this and the symmetry of the comparison angle in its two arguments, the upper angle is a genuine pseudometric on directions, and the space of directions at $p$ is its metric quotient.
-- source:
--   Standard metric geometry. The Alexandrov (upper) angle is Definition I.1.12 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319; its behaviour on a geodesic line is Remark I.1.13(2), the value in a metric tree is Remark I.1.13(3), and the triangle inequality making it a pseudometric is Proposition I.1.14. Proposition II.3.1 shows that in a CAT(k) space the defining limit superior is a limit. The space of directions is treated in Chapter II.3. Mathlib has no comparison angle and no angle between curves.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_geodesicLine_self_eq_zero {X : Type*} [PseudoMetricSpace X]
    (gamma : ℝ → X) (h : IsGeodesicLine gamma) :
    alexandrovAngle (gamma 0) gamma gamma = 0 := by sorry

end MetricGeometry
