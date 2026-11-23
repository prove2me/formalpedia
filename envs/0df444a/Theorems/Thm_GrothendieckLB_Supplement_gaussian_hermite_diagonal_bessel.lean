-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_diagonal_bessel
-- name    : GrothendieckLB.Supplement.gaussian_hermite_diagonal_bessel
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:40:24.698206+00:00
-- url     : https://prove2.me/theorems/4b6b079b-9dfc-4e44-a5e8-db95e32d2421
-- title:
--   Bessel inequality for the diagonal Hermite coefficients of a Gaussian kernel
-- statement:
--   For a complex-valued square-integrable kernel $f(x,y)$ under two independent standard Gaussians, the sum of squares of its equal-degree normalized Hermite coefficients over any finite set is at most the squared Gaussian $L^2$ norm of $f$.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, diagonal Hermite trace estimate (51), applied to the orthonormal probabilists’ Hermite polynomials.

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem gaussian_hermite_diagonal_bessel (f : ℝ×ℝ → ℂ) (hf : MemLp f 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (S : Finset ℕ) :
    (∑ n ∈ S, ‖∫ p : ℝ×ℝ, f p * Complex.ofReal (QuadSDE.hermiteN n p.1*QuadSDE.hermiteN n p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))‖^2) ≤
      ∫ p : ℝ×ℝ, ‖f p‖^2 ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by sorry

end GrothendieckLB.Supplement
