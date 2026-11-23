-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_integration_by_parts
-- name    : GrothendieckLB.Supplement.gaussian_hermite_integration_by_parts
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:52:24.720803+00:00
-- url     : https://prove2.me/theorems/6e8d1b6b-1abc-4fce-bb73-199828317d6d
-- title:
--   Gaussian integration by parts raises the normalized Hermite degree
-- statement:
--   Let $f$ be a complex-valued continuously differentiable function on the real line, with $f$ and $f\prime$ bounded by a polynomial. For the standard Gaussian $\gamma$ and normalized probabilists’ Hermite polynomial $\psi_n$, the Gaussian coefficient of $f\prime$ satisfies $\int f\prime\psi_n\,d\gamma=\sqrt{n+1}\int f\psi_{n+1}\,d\gamma$.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, Lemma C.2; Gaussian integration by parts with normalized probabilists’ Hermite polynomials.

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.RealDeriv

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem gaussian_hermite_integration_by_parts (f g : ℝ → ℂ) (hg : Continuous g) (hd : ∀ x : ℝ, HasDerivAt f (g x) x)
    (C : ℝ) (k : ℕ) (hb : ∀ x : ℝ, ‖f x‖+‖g x‖≤C*(1+x^2)^k) (n : ℕ) :
    (∫ x : ℝ, g x*Complex.ofReal (QuadSDE.hermiteN n x) ∂gaussianReal 0 1) =
      Complex.ofReal (Real.sqrt (n+1:ℝ)) *
        ∫ x : ℝ, f x*Complex.ofReal (QuadSDE.hermiteN (n+1) x) ∂gaussianReal 0 1 := by sorry

end GrothendieckLB.Supplement
