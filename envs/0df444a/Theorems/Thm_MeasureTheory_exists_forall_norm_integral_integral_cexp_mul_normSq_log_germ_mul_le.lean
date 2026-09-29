-- Prove2me | Theorems.Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
-- name    : MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/9bf10c02-39b3-5dc9-b8ae-b28839f8376d
-- title:
--   Decay of a mixed Fourier transform of ρ²logρ germ
-- statement:
--   Fix a real number $R$ with $0\le R$. The assertion is that there exists a constant $K\ge 0$, depending only on $R$, with the following property. Let $h:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be infinitely differentiable in the real sense, vanish at every point $p$ with $R<|p_1|$, and satisfy $h(p_1,p_2+1)=h(p_1,p_2)$ for all $p$; let $M$ be a real number such that $\|\,\mathrm{iteratedFDeriv}_{\mathbb{R}}^{\,n}h(p)\|\le M$ for every order $n\le 6$ and every $p\in\mathbb{R}^2$. Then for every $\xi\in\mathbb{R}$ and every $m\in\mathbb{Z}$,
--   $$\Bigl\|\int_{\mathbb{R}}\int_{[0,1)} e^{-2\pi i(\xi x+m\theta)}\,\bigl|1-e^{x/2+2\pi i\theta}\bigr|^{2}\log\bigl|1-e^{x/2+2\pi i\theta}\bigr|\;h(x,\theta)\,d\theta\,dx\Bigr\|\le K\,M\,(1+|\xi|)^{-2}\,\bigl(1+|m|\bigr)^{-3/2},$$
--   the inner integral being over the set $\mathrm{Ico}\,0\,1$ and the real factor $|1-e^{x/2+2\pi i\theta}|^{2}\log|1-e^{x/2+2\pi i\theta}|$ being coerced into $\mathbb{C}$. The exponent $2$ in $\xi$ and the exponent $3/2$ in $m$ are as stated, and $K$ is independent of $h$, $M$, $\xi$ and $m$.
--
--   This is the quantitative decay estimate for the two-dimensional Fourier coefficients of the logarithmic germ $|1-e^{x/2+2\pi i\theta}|^{2}\log|1-e^{x/2+2\pi i\theta}|$ cut off by a smooth, $\theta$-periodic, horizontally compactly supported window, the constant being linear in the $C^{6}$-bound $M$ of the window. It is used to produce summability of the mixed Fourier modes in [`MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic`](thm.html#MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic); the proof combines the splitting of the germ into $\rho^{2}\log\rho$ times a smooth factor plus a smooth remainder ([`Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add`](thm.html#Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add), [`Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le`](thm.html#Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le)) with the smooth and singular oscillatory-integral bounds [`MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic`](thm.html#MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic) and [`MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log`](thm.html#MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := by sorry
