-- Prove2me | Theorems.Thm_Komlos_gaussian_cube_half_measure
-- name    : Komlos.gaussian_cube_half_measure
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:34:11.485474+00:00
-- url     : https://prove2.me/theorems/a6a9d0b3-fc3f-4d02-8a2a-2e231df9bf56
-- title:
--   A logarithmic-radius cube has Gaussian measure at least one half
-- statement:
--   For every integer $m\ge0$, let $\gamma_m$ be standard Gaussian probability measure on $\mathbb R^m$. Then the closed coordinate cube of radius $2\sqrt{\log(m+2)}$ satisfies
--   $$\gamma_m\!\left(\left\{x\in\mathbb R^m:\ |x_j|\le2\sqrt{\log(m+2)}\text{ for all }j\right\}\right)\ge\frac12.$$
--   The assertion includes dimension zero, where the coordinate condition is vacuous and the Gaussian measure is one. This quantitative Gaussian estimate supplies the measure hypothesis when Banaszczyk’s convex-body balancing theorem is applied to a cube.
-- source:
--   Quantitative version of the cube Gaussian-measure observation on p. 3 after Theorem 1.1 of Dadush–Garg–Lovett–Nikolov, Theory of Computing 15(15), 2019, https://theoryofcomputing.org/articles/v015a015/v015a015.pdf . The explicit radius 2 sqrt(log(m+2)) is certified in the accompanying Gaussian-tail and union-bound proof.

import Definitions.Def_Komlos_model
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Komlos

theorem gaussian_cube_half_measure (m : ℕ) :
    (1/2 : ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real
      {x | ∀ j, |x j| ≤ 2 * Real.sqrt (Real.log ((m:ℝ)+2))} := by sorry

end Komlos
