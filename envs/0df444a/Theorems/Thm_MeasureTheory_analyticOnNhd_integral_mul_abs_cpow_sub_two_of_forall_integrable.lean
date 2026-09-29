-- Prove2me | Theorems.Thm_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
-- name    : MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/370fbd60-4b96-5da2-b71f-d216c6014c53
-- title:
--   Analyticity and positivity of a two-sided Mellin transform
-- statement:
--   Let $P:\mathbb{R}\to\mathbb{R}$ be measurable with $P(y)\ge 0$ for all $y$, and let $x_0\in\mathbb{R}$ be such that for every real $\sigma>x_0$ the function $y\mapsto P(y)\,|y|^{\sigma-2}$ is Lebesgue integrable on $\mathbb{R}$. Consider the complex-valued function $M(s)=\int_{\mathbb{R}} P(y)\,|y|^{s-2}\,dy$, the integrand being formed with the complex power of the non-negative real $|y|$ and the exponent $s-2$. Then three assertions hold. First, $M$ is analytic at every point of the open half-plane $\{s\in\mathbb{C}: \operatorname{Re} s>x_0\}$, in the sense that each such point has a neighbourhood on which $M$ is given by a convergent power series. Second, for every real $\sigma>x_0$ the value $M(\sigma)$ (the exponent being $(\sigma:\mathbb{C})-2$) has vanishing imaginary part and non-negative real part. Third, if it is not the case that $P(y)=0$ for almost every $y$, then for every real $\sigma>x_0$ the real part of $M(\sigma)$ is strictly positive.
--
--   This is the standard statement that the two-sided Mellin transform of a non-negative weight is holomorphic on its half-plane of absolute convergence and takes real, non-negative — indeed strictly positive unless the weight vanishes almost everywhere — values at real points. It is used in the Rankin–Selberg package over $\mathbb{Q}$, where such integrals arise as archimedean factors attached to a torus profile and are compared with Gamma factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.analyticOnNhd_integral_mul_abs_cpow_sub_two_of_forall_integrable
    (P : ℝ → ℝ) (x₀ : ℝ) (hP : Measurable P) (hP0 : ∀ y : ℝ, 0 ≤ P y)
    (hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) {s : ℂ | x₀ < s.re} ∧
    (∀ σ : ℝ, x₀ < σ →
      (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).im = 0 ∧
      0 ≤ (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) ∧
    ((¬ ∀ᵐ y : ℝ, P y = 0) → ∀ σ : ℝ, x₀ < σ →
      0 < (∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ ((σ : ℂ) - 2)).re) := by sorry
