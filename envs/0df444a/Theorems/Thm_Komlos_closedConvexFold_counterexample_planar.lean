-- Prove2me | Theorems.Thm_Komlos_closedConvexFold_counterexample_planar
-- name    : Komlos.closedConvexFold_counterexample_planar
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:31:01.66885+00:00
-- url     : https://prove2.me/theorems/6e0415f2-ac3b-4ab3-9047-adf10b26e1af
-- title:
--   Ehrhard reduction of a failed convex-fold inequality to a planar counterexample
-- statement:
--   Let $K\subseteq\mathbb R^m$ be compact and convex, with standard Gaussian measure $\gamma_m(K)\ge1/2$, and let $\|u\|\le1/5$. Let $F_u(K)$ be its explicit closed convex fold. Write $g(x)=e^{-x^2/2}$, $T(x)=\int_x^\infty g(s)\,ds$, and $A_r(x)=\int_x^{x+r}g(s)\,ds$. For real parameters define
--   $$B(w,d,b)=\int_0^\infty g(w+d+x)T\bigl(b(d+x)\bigr)\,dx,$$
--   $$G(w,d,b,r)=\int_0^\infty g(w-x)A_r(bx)\,dx+\int_0^d g(w+x)A_r(-bx)\,dx.$$
--   If $\gamma_m(F_u(K))<\gamma_m(K)$, then there are $w,d,b,r\ge0$ satisfying
--   $$r\le1/5,\qquad T(bd)\le2A_r(0),\qquad G(w,d,b,r)<B(w,d,b).$$
--   This isolates the geometric reduction from a general convex body to the planar strip comparison. It includes the Gaussian symmetrization and the comparison-line construction; the scalar Gaussian integral inequality is a separate theorem.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Section 3.2.1. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . Proof of Theorem 15, Steps 1-3, printed pp. 19-22, in particular Lemmas 16-18 and the setup of Lemma 19. This is the counterexample form of those reductions, with b=-k, x*=w+d, and r=norm(u). The closed-fold formulation only enlarges the geometric fold. A proof must also discharge m=0, m=1, u=0, endpoint/empty slices, and limiting cases; these are not removed by extra hypotheses.

import Definitions.Def_Komlos_gaussian_fold_analysis
import Definitions.Def_Komlos_convex_fold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open Set MeasureTheory ProbabilityTheory GaussianFoldAnalysis
open scoped intervalIntegral
set_option autoImplicit false

theorem Komlos.closedConvexFold_counterexample_planar
    (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K)
    (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ ≤ (1/5:ℝ))
    (hcounter : (stdGaussian (EuclideanSpace ℝ (Fin m))).real (Komlos.closedConvexFold m K u) <
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real K) :
    ∃ w d b r : ℝ, 0 ≤ w ∧ 0 ≤ d ∧ 0 ≤ b ∧ 0 ≤ r ∧ r ≤ 1/5 ∧
      tail (b * d) ≤ 2 * intervalMass r 0 ∧
      (∫ x in Ioi (0 : ℝ), kernel (w - x) * intervalMass r (b * x)) +
        (∫ x in (0 : ℝ)..d, kernel (w + x) * intervalMass r (-b * x)) <
      ∫ x in Ioi (0 : ℝ), kernel (w + d + x) * tail (b * (d + x)) := by sorry
