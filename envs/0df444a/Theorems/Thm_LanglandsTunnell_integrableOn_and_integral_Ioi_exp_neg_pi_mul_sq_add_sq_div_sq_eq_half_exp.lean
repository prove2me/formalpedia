-- Prove2me | Theorems.Thm_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
-- name    : LanglandsTunnell.integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/763789e8-e3f6-5aea-a0ef-44a122f4ea61
-- title:
--   Cauchy–Schlömilch Gaussian integral int₀^∞ e^{-π(w^2+ρ^2/w^2)} dw=tfrac12 e^{-2πρ}
-- statement:
--   Let $\rho$ be a real number with $0<\rho$. The assertion is the conjunction of two statements about the function $w\mapsto \exp\bigl(-(\pi(w^{2}+\rho^{2}/w^{2}))\bigr)$ on the reals: first, that this function is integrable on the open half-line $(0,\infty)$ with respect to Lebesgue measure restricted to that set; and second, that its Lebesgue integral over $(0,\infty)$ equals $\tfrac12\exp(-2\pi\rho)$. Here the integrand is the real exponential of $-(\pi(w^{2}+\rho^{2}/w^{2}))$, with the quotient $\rho^{2}/w^{2}$ understood as division of real numbers, so that the integrand takes the value $\exp(-\pi\cdot 0)=1$ at $w=0$; this value is irrelevant to both conclusions, since the domain of integration is the open interval $(0,\infty)$.
--
--   This is the classical Cauchy–Schlömilch evaluation of the Gaussian-type integral $\int_0^\infty e^{-a w^{2}-b/w^{2}}\,dw$ in the case $a=\pi$, $b=\pi\rho^{2}$. It supplies the one-dimensional radial computation used in the fibre evaluation of a Rankin–Selberg type integral, and is cited by [`LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous`](thm.html#LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp.lean

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
    (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2)))) (Ioi 0) ∧
      ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) =
        (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * ρ)) := by sorry
