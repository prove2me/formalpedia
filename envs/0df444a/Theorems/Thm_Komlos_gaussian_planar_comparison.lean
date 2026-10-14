-- Prove2me | Theorems.Thm_Komlos_gaussian_planar_comparison
-- name    : Komlos.gaussian_planar_comparison
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:30:59.310687+00:00
-- url     : https://prove2.me/theorems/1645f4a9-d16b-45c7-82e4-0cec4da2d3ed
-- title:
--   Gaussian half-plane mass is bounded by the comparison strip
-- statement:
--   Write $g(x)=e^{-x^2/2}$, $T(x)=\int_x^\infty g(s)\,ds$, and $A_r(x)=\int_x^{x+r}g(s)\,ds$. For real parameters define
--   $$B(w,d,b)=\int_0^\infty g(w+d+x)T\bigl(b(d+x)\bigr)\,dx,$$
--   $$G(w,d,b,r)=\int_0^\infty g(w-x)A_r(bx)\,dx+\int_0^d g(w+x)A_r(-bx)\,dx.$$
--   If $w,d,b,r\ge0$, $r\le1/5$, and $T(bd)\le2A_r(0)$, then
--   $$B(w,d,b)\le G(w,d,b,r).$$
--   These are the unnormalized Gaussian masses of the lost half-plane region and the comparison strip in the planar step of the convex-fold argument. The common normalization factor is omitted.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Section 3.2.1. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . Lemma 19, printed p. 22, with its scalar estimates in Lemmas 20-21, pp. 23-24. Here b=-k is the nonnegative opposite of the source line slope, d is the horizontal offset from its zero, and w is that zero. The integral coordinates translate the lost region and reflect the left part of the gained strip. Zero boundary cases are included; the supplied hypotheses make b=0 or d=0 impossible.

import Definitions.Def_Komlos_gaussian_fold_analysis
import Definitions.Def_Komlos_convex_fold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open Set MeasureTheory ProbabilityTheory GaussianFoldAnalysis
open scoped intervalIntegral
set_option autoImplicit false

theorem Komlos.gaussian_planar_comparison (w d b r : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 5)
    (hbase : tail (b * d) ≤ 2 * intervalMass r 0) :
    (∫ x in Ioi (0 : ℝ), kernel (w + d + x) * tail (b * (d + x))) ≤
      (∫ x in Ioi (0 : ℝ), kernel (w - x) * intervalMass r (b * x)) +
      ∫ x in (0 : ℝ)..d, kernel (w + x) * intervalMass r (-b * x) := by sorry
