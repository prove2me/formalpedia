-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
-- name    : LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/24308ddc-8c5a-5075-bef7-ad1cc8555a93
-- title:
--   Fubini over the hyperbolic region σ,w>0, σ w>v
-- statement:
--   Let $v$ be a real number with $v>0$, let $f\colon\mathbb R\times\mathbb R\to\mathbb C$, and write $R=\{q\in\mathbb R\times\mathbb R : 0<q_1,\ 0<q_2,\ v<q_1q_2\}$ for the region above the hyperbola in the open first quadrant. Assume $f$ is integrable on $R$ with respect to Lebesgue measure on $\mathbb R\times\mathbb R$ (`IntegrableOn f R`). The conclusion is the conjunction of two equalities of Bochner integrals: first, $$\int_{\sigma\in(0,\infty)}\Big(\int_{w\in(v/\sigma,\infty)} f(\sigma,w)\,dw\Big)d\sigma=\int_{q\in R} f(q)\,dq,$$ and second, with the order of integration exchanged, $$\int_{w\in(0,\infty)}\Big(\int_{\sigma\in(v/w,\infty)} f(\sigma,w)\,d\sigma\Big)dw=\int_{q\in R} f(q)\,dq.$$ All integrals are set integrals against Lebesgue measure, the inner integrals being over the open rays $(v/\sigma,\infty)$, respectively $(v/w,\infty)$; the outer ones over $(0,\infty)$. Thus both iterated integrals over the non-rectangular region $R$, in either order, agree with the integral of $f$ over $R$.
--
--   This is Fubini's theorem for the region above a hyperbola in the open quadrant, with the fibres identified explicitly: for $\sigma>0$ the fibre of $R$ is the ray $(v/\sigma,\infty)$, since $v>0$ already forces $w>0$, and symmetrically in $w$. It is the order-of-exchange step used in the evaluation of an integral of a homogeneous expression against a Gaussian average, cited by [`LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous`](thm.html#LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.lean

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
    (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by sorry
