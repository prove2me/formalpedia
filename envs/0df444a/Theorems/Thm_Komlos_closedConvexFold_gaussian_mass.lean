-- Prove2me | Theorems.Thm_Komlos_closedConvexFold_gaussian_mass
-- name    : Komlos.closedConvexFold_gaussian_mass
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:55:08.373037+00:00
-- url     : https://prove2.me/theorems/9845d72a-c949-4d72-8cec-d34917f3145b
-- title:
--   Gaussian measure increases under the explicit closed fold
-- statement:
--   Let $K\subseteq\mathbb R^m$ be compact and convex with standard Gaussian measure $\gamma_m(K)\ge1/2$. For any vector $u$ with $\|u\|_2\le1/5$, its explicit closed fold satisfies
--   $$\gamma_m\bigl(F_u(K)\bigr)\ge\gamma_m(K).$$
--   Here $F_u(K)=\overline{(K+[-u,u])\cap(C_u(K)+\mathbb Ru)}$, where $C_u(K)=\{y\in K:y+2u\in K\}$. This is the analytic estimate in Banaszczyk's folding argument; compactness, convexity, and translate containment are handled by a separate geometric theorem.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Theorem 15, printed p. 18; proof in Section 3.2.1, printed pp. 19–24. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . The algebraic definition records the closed version of Definition 14. Closure can only increase Gaussian measure; the zero vector gives F_0(K)=K for closed K.

import Definitions.Def_Komlos_convex_fold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open Set MeasureTheory ProbabilityTheory
open scoped Pointwise
set_option autoImplicit false

theorem Komlos.closedConvexFold_gaussian_mass (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K)
    (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ ≤ (1/5:ℝ)) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real K ≤
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real (Komlos.closedConvexFold m K u) := by sorry
