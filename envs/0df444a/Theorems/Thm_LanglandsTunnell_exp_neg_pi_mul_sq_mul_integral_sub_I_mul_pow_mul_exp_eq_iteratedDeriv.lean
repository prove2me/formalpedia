-- Prove2me | Theorems.Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
-- name    : LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/da7155d1-fbf7-5cac-9842-fd01db02637f
-- title:
--   Rodrigues formula for Gaussian moments of σ-iz
-- statement:
--   For every natural number $n$ and every real number $\sigma$, consider the complex-valued function $s\mapsto e^{-\pi s^{2}}$ of a real variable, and the integral over $\mathbb{R}$, with respect to Lebesgue measure, of the complex-valued integrand $z\mapsto(\sigma-iz)^{n}e^{-\pi z^{2}}$, where $\sigma$ and $z$ are coerced into $\mathbb{C}$ and $i$ is the imaginary unit. The assertion is the identity
--   $$e^{-\pi\sigma^{2}}\int_{\mathbb{R}}(\sigma-iz)^{n}e^{-\pi z^{2}}\,dz=\bigl(-(2\pi)\bigr)^{-n}\,\frac{d^{n}}{ds^{n}}\Bigl(e^{-\pi s^{2}}\Bigr)\Big|_{s=\sigma},$$
--   in which the left-hand factor $e^{-\pi\sigma^{2}}$ is the real exponential coerced into $\mathbb{C}$, the scalar on the right is the $n$-th power of the inverse in $\mathbb{C}$ of $-(2\pi)$, and the derivative is the $n$-fold iterated derivative, in the sense of `iteratedDeriv`, of the complex-valued Gaussian $s\mapsto e^{-\pi s^{2}}$ regarded as a function on $\mathbb{R}$, evaluated at $\sigma$. No hypotheses beyond the two arguments $n$ and $\sigma$ are imposed; in particular the integrability of the integrand is not assumed but is part of what makes the identity meaningful.
--
--   This is Rodrigues' formula for the Hermite polynomials attached to the Gaussian weight $e^{-\pi s^{2}}$, expressed as the statement that the $n$-th moment of the complex shift $\sigma-iZ$ against the Gaussian equals $e^{\pi\sigma^{2}}(-2\pi)^{-n}\partial_\sigma^{n}e^{-\pi\sigma^{2}}$. It serves as the elementary Gaussian input to the fibre evaluations in the Rankin–Selberg integral computations, being used in the integrability and torus-integral lemmas for harmonic Gaussian test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv.lean

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
    (n : ℕ) (σ : ℝ) :
    (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
        ∫ z : ℝ, ((σ : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      (-(2 * (Real.pi : ℂ)))⁻¹ ^ n * iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ := by sorry
