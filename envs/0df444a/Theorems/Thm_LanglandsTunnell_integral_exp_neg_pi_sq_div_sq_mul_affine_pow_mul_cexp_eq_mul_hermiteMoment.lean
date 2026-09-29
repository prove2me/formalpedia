-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
-- name    : LanglandsTunnell.integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/dee5f204-a63a-5986-a821-b02532d3c462
-- title:
--   Twisted Gaussian moment as a shifted Hermite integral
-- statement:
--   Let $\alpha, c$ be real numbers, let $y_1$ be a nonzero real number and let $m$ be a natural number. The assertion is an identity between two complex-valued integrals over $\mathbb{R}$ with respect to the Lebesgue measure (Bochner integrals of $\mathbb{C}$-valued functions). On the left stands the integral over $x \in \mathbb{R}$ of $e^{-\pi x^2 / y_1^2}\,(\alpha + i y_1^{-1} x)^m\, e^{2\pi i c x}$, where the real Gaussian factor $e^{-\pi(x^2/y_1^2)}$ is coerced into $\mathbb{C}$, the middle factor is the $m$-th power of the complex affine function $\alpha + i(1/y_1)x$, and the last factor is the complex exponential $\exp(2\pi i c x)$. The claim is that this equals $|y_1| \cdot e^{-\pi c^2 y_1^2}$ times the integral over $u \in \mathbb{R}$ of $e^{-\pi u^2}\,(\alpha - c y_1 + i u)^m$, the scalar factors again being real numbers coerced into $\mathbb{C}$. Thus the scale $y_1$ and the additive character parameter $c$ are absorbed into the prefactor $|y_1| e^{-\pi c^2 y_1^2}$ and the shift of the argument from $\alpha$ to $\alpha - c y_1$.
--
--   The right-hand integral is the monic Hermite polynomial of variance $1/2\pi$ evaluated at $\alpha - c y_1$, so the statement computes a degree-$m$ twisted Gaussian moment in closed Hermite form. It is used to evaluate the archimedean $x$-integral occurring in the Whittaker/Jacquet vector computations for the cubic induction step, in the two results that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment.lean

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Complex FourierTransform

theorem LanglandsTunnell.integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
    (α c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (m : ℕ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (((α : ℝ) : ℂ) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) * (x : ℂ)) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) *
        ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * ((((α - c * y₁ : ℝ)) : ℂ) + Complex.I * (u : ℂ)) ^ m := by sorry
