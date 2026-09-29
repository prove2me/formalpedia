-- Prove2me | Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc
-- name    : MetricGeometry.comparisonAngle_mem_Icc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T21:19:34.853173+00:00
-- url     : https://prove2.me/theorems/7788efe3-6bd9-4144-8796-0c10e394132a
-- title:
--   The comparison angle lies in $[0,\pi]$
-- statement:
--   The comparison angle at $p$ in a triangle $p,x,y$ takes values in $[0,\pi]$:
--
--   $$
--   0\;\le\;\widetilde\angle_p(x,y)\;\le\;\pi .
--   $$
--
--   The comparison angle is defined as the arccosine of the law-of-cosines quotient, and the arccosine of any real number lies in $[0,\pi]$ — Lean's `Real.arccos` clamps its argument to $[-1,1]$ before inverting, so no hypothesis on the quotient is required.
--
--   The statement is elementary but not idle: the quotient is only guaranteed to lie in $[-1,1]$ at genuine triangles, where it does by the triangle inequality, and the range statement is what allows comparison angles to be manipulated as angles — compared, added, passed to limits — without carrying a nondegeneracy hypothesis at every step.
-- source:
--   Standard metric geometry. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (geodesics), I.2.13 (the law of cosines in Euclidean space), Lemma I.2.14 (existence of comparison triangles), and Proposition II.1.4(1) (uniqueness of geodesics in a CAT(0) space). The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has none of this: no metric midpoint, no synthetic curvature condition, no geodesic in a metric space, no comparison angle and no metric cone.

import Definitions.Def_metric_geodesic_angle

namespace MetricGeometry

theorem comparisonAngle_mem_Icc {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    0 ≤ comparisonAngle p x y ∧ comparisonAngle p x y ≤ Real.pi := by sorry

end MetricGeometry
