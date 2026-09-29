-- Prove2me | Theorems.Thm_MetricGeometry_alexandrovAngle_triangle
-- name    : MetricGeometry.alexandrovAngle_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:11:35.344118+00:00
-- url     : https://prove2.me/theorems/ac97338f-d8e5-4c43-905d-6d2349de4fe6
-- title:
--   The Alexandrov angle satisfies the triangle inequality
-- statement:
--   Let $X$ be a metric space and let $c,c',c''$ be three geodesic paths issuing from a common point $p$, each
--   parametrised by arclength on $(0,a]$, so that $d(p,c(t))=d(p,c'(t))=d(p,c''(t))=t$ for $0<t\le a$. Then the
--   Alexandrov (upper) angle satisfies the triangle inequality:
--
--   $$\angle(c',c'')\ \le\ \angle(c,c')+\angle(c,c'').$$
--
--   **Role.** This is Alexandrov's theorem, and it is what makes the theory of angles in metric spaces possible. The
--   Alexandrov angle is defined as a $\limsup$ of comparison angles,
--
--   $$\angle(c_1,c_2)=\limsup_{s,t\to 0^+}\widetilde\angle_p\bigl(c_1(s),c_2(t)\bigr),$$
--
--   and it is symmetric and nonnegative for trivial reasons; the triangle inequality is the one axiom of a
--   pseudometric that requires an argument. Once it is available, "having angle $0$" is an equivalence relation on
--   the geodesics issuing from $p$, the quotient carries a genuine metric, and its completion is the *space of
--   directions* $\Sigma_pX$ — the object on which the local structure theory of spaces of curvature bounded above,
--   and in particular the identification of the links of a Euclidean building as spherical buildings, is built.
--
--   The $\limsup$ is essential: with $\liminf$ in place of $\limsup$ the property fails.
--
--   **The argument.** All the geometry is in a finite statement with no limits: if a curve $c$ parametrised by
--   arclength from $p$ satisfies $\widetilde\angle_p(c(t),b)\le A$ and $\widetilde\angle_p(c(t),e)\le B$ for every
--   $t$ up to $\max(d(p,b),d(p,e))$, then $\widetilde\angle_p(b,e)\le A+B$. Given that, fix $\delta>0$; by
--   definition of $\limsup$ there is an $\varepsilon>0$ such that $\widetilde\angle_p(c(s),c'(t))<\angle(c,c')+\delta$
--   and $\widetilde\angle_p(c(s),c''(t))<\angle(c,c'')+\delta$ whenever $s,t<\varepsilon$. Applying the finite
--   statement to $b=c'(t')$ and $e=c''(t'')$ for $t',t''<\varepsilon$ — whose distances to $p$ are $t'$ and $t''$,
--   both below $\varepsilon$, so the whole curve segment used is within range — bounds
--   $\widetilde\angle_p(c'(t'),c''(t''))$ by $\angle(c,c')+\angle(c,c'')+2\delta$ for all such $t',t''$. Taking the
--   $\limsup$ and then $\delta\to0$ gives the claim.
--
--   **Formalization Note.** The hypothesis is stated as arclength parametrisation on a half-open interval $(0,a]$
--   rather than through a geodesic predicate; this is exactly what the proof uses, and it covers geodesic segments,
--   rays and lines restricted to positive parameters. The value of $\limsup$ depends only on the germ of the curves
--   at $0^+$, so the restriction to $(0,a]$ costs nothing.
-- source:
--   Proposition I.1.14 (due to Alexandrov [Ale51]) of M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), which together with symmetry and positivity shows that the Alexandrov angle of Definition I.1.12 is a pseudometric on the geodesics issuing from a point.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

theorem alexandrovAngle_triangle {X : Type*} [PseudoMetricSpace X] (p : X)
    (c c' c'' : ℝ → X) (a : ℝ) (ha : 0 < a)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c t) = t)
    (hc' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c' t) = t)
    (hc'' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c'' t) = t) :
    alexandrovAngle p c' c'' ≤ alexandrovAngle p c c' + alexandrovAngle p c c'' := by sorry

end MetricGeometry
