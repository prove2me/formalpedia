-- Prove2me | Theorems.Thm_Komlos_banaszczyk_convex_fold
-- name    : Komlos.banaszczyk_convex_fold
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:43:13.306499+00:00
-- url     : https://prove2.me/theorems/a80dff41-e2de-4c44-9606-58ec048b0a00
-- title:
--   The Gaussian-measure-preserving convex fold for a short vector
-- statement:
--   Let $m\ge0$, let $K\subseteq\mathbb R^m$ be compact and convex with standard Gaussian measure $\gamma_m(K)\ge1/2$, and let $u\in\mathbb R^m$ satisfy $\|u\|_2\le1/5$. There exists a compact convex set $L\subseteq\mathbb R^m$ such that
--   $$\gamma_m(L)\ge\gamma_m(K),\qquad L\subseteq(K-u)\cup(K+u).$$
--   Equivalently, every $x\in L$ satisfies $x+u\in K$ or $x-u\in K$. No symmetry of either set is required. This single-vector geometric statement is the measure-preserving induction step in Banaszczyk’s vector-balancing argument; applying it successively absorbs the vectors while retaining a Gaussian-large convex set.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Definition 14 and Theorem 15, printed p. 18 (PDF p. 35); proof in Section 3.2.1, printed pp. 19–24. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . This gives the exact norm threshold 1/5 and Gaussian-measure monotonicity of K*u. The theorem here records existence of the convex folded set; for compact K one may take the closure inside the closed compact union (K-u) union (K+u). Also described on p. 3 of Dadush–Garg–Lovett–Nikolov, Theory of Computing 15(15), 2019, https://theoryofcomputing.org/articles/v015a015/v015a015.pdf . Original result: Banaszczyk 1998.

import Definitions.Def_Komlos_model
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Komlos

theorem banaszczyk_convex_fold (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K)
    (u : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ ≤ (1/5:ℝ)) :
    ∃ L : Set (EuclideanSpace ℝ (Fin m)), Convex ℝ L ∧ IsCompact L ∧
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real K ≤
        (stdGaussian (EuclideanSpace ℝ (Fin m))).real L ∧
      ∀ x ∈ L, x+u ∈ K ∨ x-u ∈ K := by sorry

end Komlos
