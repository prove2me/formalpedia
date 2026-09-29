-- Prove2me | Theorems.Thm_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
-- name    : LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0ab4e216-08c3-58cc-ada7-4d96d94697c4
-- title:
--   Fibre integral of a Gaussian average over a hyperbolic region
-- statement:
--   Let $m$ be a natural number, $a$ a complex number with $\operatorname{Re} a > m-1$, $v$ a positive real, and $p \in \mathbb{C}[X_0,X_1]$ (a polynomial in two variables, indexed by `Fin 2`) homogeneous of degree $m$ in the sense of `MvPolynomial.IsHomogeneous`. The assertion is the identity of iterated integrals $$\int_{0}^{\infty}\!\!\int_{v/\sigma}^{\infty} (\sigma w - v)^{a}\, w^{\,1-m}\, e^{-\pi(\sigma^{2}+w^{2})} \Bigl(\int_{\mathbb{R}} p(\sigma - i z,\, w)\, e^{-\pi z^{2}}\,dz\Bigr) dw\, d\sigma = \tfrac{1}{2}\,(2\pi)^{-a-1}\,\Gamma(a+1)\, e^{-2\pi v}\, p(1,1).$$ Here the outer variable $\sigma$ ranges over $(0,\infty)$ and the inner variable $w$ over $(v/\sigma,\infty)$, so that the real number $\sigma w - v$ is positive and $(\sigma w - v)^{a}$ is its complex power after coercion, $w^{1-m}$ is the integer power $(w:\mathbb{C})^{1-m}$, the innermost integral is over all of $\mathbb{R}$ with respect to the Gaussian weight $e^{-\pi z^{2}}$ of total mass $1$, and $\Gamma$ is the complex Gamma function. In particular the left-hand side vanishes whenever $p(1,1) = 0$, and it depends on $p$ only through $p(1,1)$.
--
--   This is the archimedean fibre evaluation used in the Langlands–Tunnell Rankin–Selberg computation: on the hyperbolic region $\{\sigma>0,\ w>0,\ \sigma w>v\}$ the displayed functional of a degree-$m$ homogeneous block polynomial reduces to evaluation at $(1,1)$ times a universal Gamma factor. It is cited by [`LanglandsTunnell.setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero`](thm.html#LanglandsTunnell.setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero), where the one-sided Whittaker profile of a discrete-series parameter is integrated over the torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
    (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) :
    ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) *
          (Real.exp (-(2 * Real.pi * v)) : ℂ) * MvPolynomial.eval ![(1 : ℂ), 1] p := by sorry
