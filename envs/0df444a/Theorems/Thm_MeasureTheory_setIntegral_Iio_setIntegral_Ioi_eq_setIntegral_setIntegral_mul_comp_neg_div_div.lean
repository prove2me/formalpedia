-- Prove2me | Theorems.Thm_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
-- name    : MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/35b2bf5e-0555-5fb6-82d7-fb0f3fd78ea3
-- title:
--   Fibre substitution (y₁,y₂)=(-u/t, u/v) for iterated integrals
-- statement:
--   Let $h\colon\mathbb{R}\to\mathbb{R}\to\mathbb{C}$ be an arbitrary function of two real variables with complex values, and let $t$ be a real number with $0<t$. Then the iterated Bochner integral of $h$ over the quadrant $(-\infty,0)\times(0,\infty)$, taken as $\int_{y_1\in(-\infty,0)}\bigl(\int_{y_2\in(0,\infty)}h(y_1,y_2)\,dy_2\bigr)dy_1$ with respect to Lebesgue measure on each variable, equals $$\int_{u\in(0,\infty)}\int_{v\in(0,\infty)}\frac{u}{t\,v^{2}}\;h\!\left(-\frac{u}{t},\,\frac{u}{v}\right)dv\,du,$$ the real factor $u/(t v^{2})$ being coerced into $\mathbb{C}$ and multiplying the value of $h$. No measurability, local integrability or integrability hypothesis is imposed on $h$; positivity of $t$ is the only assumption. The identity is thus the change of variables $(y_1,y_2)=(-u/t,\,u/v)$, a bijection of $(0,\infty)^2$ onto $(-\infty,0)\times(0,\infty)$ with Jacobian factor $u/(t v^{2})$, stated at the level of iterated integrals rather than for an integral over the product measure.
--
--   This is the one-variable-at-a-time change of variables (fibre substitution at fixed $t$) turning an integral over $(-\infty,0)\times(0,\infty)$ into one over the positive quadrant. It is used as the first step of [`LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber`](thm.html#LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber), where the substitution introduces the fibre coordinates $u=t|y_1|$ and $v=t|y_1|/y_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
    (h : ℝ → ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂ =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * h (-(u / t)) (u / v) := by sorry
