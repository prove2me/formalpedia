-- Prove2me | Theorems.Thm_Komlos_gaussian_closed_convex_contains_zero
-- name    : Komlos.gaussian_closed_convex_contains_zero
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:43:10.796699+00:00
-- url     : https://prove2.me/theorems/a7041dad-9e79-45c7-802a-0abd99fb66d0
-- title:
--   Closed convex sets of Gaussian measure at least one half contain the origin
-- statement:
--   Let $m\ge0$ and let $\gamma_m$ be standard Gaussian probability measure on $\mathbb R^m$. Every closed convex set $K\subseteq\mathbb R^m$ satisfying $\gamma_m(K)\ge1/2$ contains the origin:
--   $$\gamma_m(K)\ge\frac12\quad\Longrightarrow\quad 0\in K.$$
--   Neither boundedness nor central symmetry of $K$ is assumed. Dimension zero is included. This is the base case for the induction underlying Banaszczyk’s vector-balancing theorem.
-- source:
--   Origin-containment observation following Theorem 1.1 and its use as the induction base, Dadush–Garg–Lovett–Nikolov, Theory of Computing 15(15), 2019, p. 3, https://theoryofcomputing.org/articles/v015a015/v015a015.pdf . The source discusses convex bodies; this contribution proves the stronger closed-convex version directly by Gaussian symmetry, convexity and full support.

import Definitions.Def_Komlos_model
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Komlos

theorem gaussian_closed_convex_contains_zero (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K) :
    (0 : EuclideanSpace ℝ (Fin m)) ∈ K := by sorry

end Komlos
