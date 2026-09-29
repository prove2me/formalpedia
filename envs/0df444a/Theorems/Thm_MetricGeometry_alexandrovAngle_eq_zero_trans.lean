-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_eq_zero_trans
-- name    : MetricGeometry.alexandrovAngle_eq_zero_trans
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:34:52.045521+00:00
-- url     : https://prove2.me/theorems/b03f71b8-14e8-4590-98d6-28c92183c774
-- title:
--   Defining the same direction is a transitive relation
-- statement:
--   Let $c,c',c''$ be geodesics issuing from a common point $p$ of a metric space, parametrised by arclength on
--   $(0,a]$. If $\angle(c,c')=0$ and $\angle(c',c'')=0$ then $\angle(c,c'')=0$.
--
--   **Role.** Two geodesics issuing from $p$ are said to *define the same direction* when the Alexandrov angle
--   between them vanishes. Reflexivity and symmetry of that relation are immediate — the angle is symmetric and
--   vanishes between a geodesic and itself — but transitivity is not: it is precisely the degenerate case of the
--   triangle inequality for angles, which is the one nontrivial fact about Alexandrov angles. This statement is
--   therefore what makes "same direction" an equivalence relation, and hence what makes the *space of directions*
--   $\Sigma_pX$ — the set of equivalence classes, metrised by the angle — well defined.
--
--   That construction is the entry point to all local structure theory in metric geometry of curvature bounded
--   above: the link of a point in a Euclidean building, the spherical building structure on it, the cone
--   decompositions near a point, and the notion of a tangent cone are all built on $\Sigma_pX$, and none of them is
--   available until the relation is known to be transitive.
--
--   **The argument.** Apply the triangle inequality for Alexandrov angles with $c'$ in the middle role:
--
--   $$\angle(c,c'')\ \le\ \angle(c',c)+\angle(c',c'').$$
--
--   By symmetry $\angle(c',c)=\angle(c,c')=0$, and $\angle(c',c'')=0$ by hypothesis, so $\angle(c,c'')\le0$. Angles
--   are nonnegative, so equality holds.
-- source:
--   The consequence of Proposition I.1.14 recorded in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1: the triangle inequality for angles implies that the relation given by vanishing of the Alexandrov angle is an equivalence relation on the geodesics issuing from a point, which is what defines the space of directions.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_eq_zero_trans {X : Type*} [PseudoMetricSpace X]
    (p : X) (c c' c'' : ℝ → X) (a : ℝ) (ha : 0 < a)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c t) = t)
    (hc' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c' t) = t)
    (hc'' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c'' t) = t)
    (h1 : alexandrovAngle p c c' = 0) (h2 : alexandrovAngle p c' c'' = 0) :
    alexandrovAngle p c c'' = 0 := by sorry

end MetricGeometry
