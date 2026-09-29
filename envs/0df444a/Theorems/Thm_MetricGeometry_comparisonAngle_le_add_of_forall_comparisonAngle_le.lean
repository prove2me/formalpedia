-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_le_add_of_forall_comparisonAngle_le
-- name    : MetricGeometry.comparisonAngle_le_add_of_forall_comparisonAngle_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:56:50.922187+00:00
-- url     : https://prove2.me/theorems/110cf8c4-73b0-4545-b144-7debf3990ee9
-- title:
--   Subadditivity of comparison angles along an arclength curve
-- statement:
--   Let $X$ be a metric space, $p\in X$, and let $b,e\in X$ be at positive distance from $p$; write
--   $m=\max\bigl(d(p,b),d(p,e)\bigr)$. Let $c$ be a curve issuing from $p$ and parametrised by arclength on
--   $(0,m]$, i.e. $d(p,c(t))=t$ for $0<t\le m$. If every point of that curve subtends a small comparison angle
--   with each of $b$ and $e$,
--
--   $$\widetilde\angle_p\bigl(c(t),b\bigr)\le A\quad\text{and}\quad \widetilde\angle_p\bigl(c(t),e\bigr)\le B
--   \qquad\text{for all }0<t\le m,$$
--
--   with $A,B\ge 0$, then
--
--   $$\widetilde\angle_p(b,e)\ \le\ A+B .$$
--
--   **Role.** This is the finite, quantitative heart of Alexandrov's theorem that the upper angle between geodesics
--   satisfies the triangle inequality. All the limiting behaviour of that theorem is packaged in its hypotheses:
--   what remains here is a statement about three points and one curve, with no limits and no filters, and it is
--   where the actual geometry happens. Passing from it to the statement about upper angles is then a routine
--   $\limsup$ argument — one applies it with $A$ and $B$ replaced by $\limsup+\delta$ and lets $\delta\to0$.
--
--   Note that no hypothesis such as $A+B<\pi$ is needed: if $A+B\ge\pi$ the conclusion is automatic, since
--   comparison angles never exceed $\pi$.
--
--   **The argument.** Suppose $\widetilde\angle_p(b,e)>A+B$ and pick $\alpha$ strictly between them; since
--   comparison angles are at most $\pi$, automatically $\alpha<\pi$. Build a Euclidean model in the plane: vectors
--   $\bar b,\bar e$ with $\|\bar b\|=d(p,b)$, $\|\bar e\|=d(p,e)$ and $\angle(\bar b,\bar e)=\alpha$. Because
--   $\alpha<\widetilde\angle_p(b,e)$, strict monotonicity of the opposite side in the comparison angle gives
--   $\|\bar b-\bar e\|<d(b,e)$.
--
--   Now split $\alpha$: choose $\alpha'$ strictly between $A$ and $\alpha-B$, which is possible exactly because
--   $A+B<\alpha$, and let $\bar x$ be the point of the segment $[\bar b,\bar e]$ with $\angle(\bar b,\bar x)=\alpha'$;
--   then $\angle(\bar x,\bar e)=\alpha-\alpha'>B$, and $\|\bar x\|\le m$. Put $t=\|\bar x\|$, which lies in $(0,m]$,
--   so the hypotheses apply at $c(t)$ and give
--   $\widetilde\angle_p(c(t),b)\le A<\alpha'$ and $\widetilde\angle_p(c(t),e)\le B<\alpha-\alpha'$. Since the
--   corresponding legs have equal lengths, strict monotonicity again yields
--   $d(c(t),b)<\|\bar x-\bar b\|$ and $d(c(t),e)<\|\bar x-\bar e\|$. As $\bar x$ lies on the segment,
--   $\|\bar b-\bar x\|+\|\bar x-\bar e\|=\|\bar b-\bar e\|$, so
--
--   $$d(b,e)\le d(b,c(t))+d(c(t),e)<\|\bar b-\bar x\|+\|\bar x-\bar e\|=\|\bar b-\bar e\|<d(b,e),$$
--
--   a contradiction.
-- source:
--   The finite geometric core of the proof of Proposition I.1.14 (the Alexandrov angle satisfies the triangle inequality, due to Alexandrov [Ale51]) in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles), with the limiting arguments stripped out and stated for a single curve and two points.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_le_add_of_forall_comparisonAngle_le {X : Type*}
    [PseudoMetricSpace X] (p b e : X) (c : ℝ → X) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 < dist p b) (he : 0 < dist p e)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)), dist p (c t) = t)
    (h1 : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)),
      comparisonAngle p (c t) b ≤ A)
    (h2 : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)),
      comparisonAngle p (c t) e ≤ B) :
    comparisonAngle p b e ≤ A + B := by sorry

end MetricGeometry
