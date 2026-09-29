-- Prove2me | Theorems.Thm_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
-- name    : MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/3e70611a-f315-586f-8fdf-c8e46cc7dc90
-- title:
--   Wedge substitution t=u(σ-u), u=v/w for iterated integrals
-- statement:
--   Let $H\colon\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be a function whose uncurried form $(t,u)\mapsto H(t,u)$ is measurable on $\mathbb{R}^2$ and integrable with respect to the product of Lebesgue measure restricted to $(0,\infty)$ with itself, and let $v$ be a real number with $v>0$. Then the iterated Bochner integral of $H$ over the open quadrant, taken with inner variable $t$ ranging over $(0,\infty)$ and outer variable $u$ ranging over $(0,\infty)$, equals the iterated integral over the wedge in which $\sigma$ ranges over $(0,\infty)$ and, for each such $\sigma$, $w$ ranges over $(v/\sigma,\infty)$, of the integrand $$\frac{v^{2}}{w^{3}}\, H\!\left(\frac{v(\sigma w-v)}{w^{2}},\ \frac{v}{w}\right),$$ the real factor $v^2/w^3$ being coerced into $\mathbb{C}$ and multiplying the value of $H$. In other words, the change of variables $t=u(\sigma-u)$, $u=v/w$, whose Jacobian factor is $v^{2}/w^{3}$, transports the iterated integral over $(0,\infty)^2$ to an iterated integral over the region $\{(\sigma,w):\sigma>0,\ w>v/\sigma\}$.
--
--   This is the plane change-of-variables step (completing the square in one variable, then inverting the other) used in Archimedean Rankin–Selberg type computations. It is the final substitution in the one-sided reduction [`LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber`](thm.html#LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber), which is its only consumer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
    (H : ℝ → ℝ → ℂ) (hHm : Measurable (Function.uncurry H))
    (hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (v : ℝ) (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w) := by sorry
