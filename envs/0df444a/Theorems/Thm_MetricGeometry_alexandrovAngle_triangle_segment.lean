-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_triangle_segment
-- name    : MetricGeometry.alexandrovAngle_triangle_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:06:31.553501+00:00
-- url     : https://prove2.me/theorems/d73c2081-da2e-43e0-9c4e-a1fa9de9e71c
-- title:
--   Triangle inequality for the angles between geodesic segments
-- statement:
--   Let $g,g',g''$ be nondegenerate geodesic segments issuing from a common point $p$ of a metric space, ending at
--   $y,y',y''$ respectively. Then the Alexandrov angles between them satisfy the triangle inequality:
--
--   $$\angle(g',g'')\ \le\ \angle(g,g')+\angle(g,g'').$$
--
--   **Role.** This is Alexandrov's theorem in the normalisation in which geodesic segments actually occur. A
--   geodesic segment $[p,y]$ carries the parametrisation on $[0,1]$ with speed $d(p,y)$, whereas the arclength form
--   of the triangle inequality requires all three curves to be parametrised with unit speed on a common interval
--   $(0,a]$. The two are related by rescaling each curve by the reciprocal of its length, and the Alexandrov angle
--   is invariant under such a rescaling, so the two statements are equivalent — but only the present one applies
--   directly to the segments $[p,y]$, $[p,y']$, $[p,y'']$ determined by three points.
--
--   Together with the symmetry of the angle and the vanishing of the angle of a nondegenerate segment with itself,
--   this makes the relation $\angle(g,h)=0$ an equivalence relation on the nondegenerate geodesic segments issuing
--   from $p$, and makes the angle a pseudometric on them. The quotient is the space of directions $\Sigma_pX$.
--
--   The nondegeneracy hypotheses cannot be dropped: for a constant segment every comparison angle in the defining
--   $\limsup$ is $\pi/2$ by the convention at a degenerate vertex, and taking $g$ constant would make the
--   right-hand side $\pi$ while saying nothing about the left.
--
--   **The argument.** Write $D=d(p,y)$, $D'=d(p,y')$, $D''=d(p,y'')$, all positive, and rescale each segment to
--   unit speed: $\hat g(t)=g(t/D)$ satisfies $d(p,\hat g(t))=t$ for $0<t\le D$, and similarly for the other two.
--   On the common interval $(0,a]$ with $a=\min(D,D',D'')$ all three are unit-speed curves issuing from $p$, so the
--   arclength form of the triangle inequality applies to them. Finally, the Alexandrov angle is unchanged by
--   rescaling parameters by positive constants, so each of the three angles for the rescaled curves equals the
--   corresponding angle for the original segments.
-- source:
--   Proposition I.1.14 of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), stated for geodesic segments normalized on the unit interval rather than parametrized by arclength.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_triangle_segment {X : Type*} [PseudoMetricSpace X]
    (p y y' y'' : X) (g g' g'' : ℝ → X)
    (hg : IsGeodesicSegment g p y) (hg' : IsGeodesicSegment g' p y')
    (hg'' : IsGeodesicSegment g'' p y'')
    (hy : dist p y ≠ 0) (hy' : dist p y' ≠ 0) (hy'' : dist p y'' ≠ 0) :
    alexandrovAngle p g' g'' ≤ alexandrovAngle p g g' + alexandrovAngle p g g'' := by
  sorry

end MetricGeometry
