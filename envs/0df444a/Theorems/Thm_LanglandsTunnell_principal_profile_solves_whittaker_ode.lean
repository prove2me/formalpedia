-- Prove2me | Theorems.Thm_LanglandsTunnell_principal_profile_solves_whittaker_ode
-- name    : LanglandsTunnell.principal_profile_solves_whittaker_ode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/a81f4e3a-f795-5654-99d7-200871053738
-- title:
--   Even principal profile solves the Whittaker equation
-- statement:
--   Let $u_1,u_2$ be complex numbers and $a_1,a_2\in\mathbb Z/2$, subject to $a_1=0$ and $a_2=0$; let $c,\nu$ be complex numbers with $c=(u_1+u_2)/2$ and $\nu=(u_1-u_2)/2$, and let $k$ be a real number with $k=0$. Let $f\colon\mathbb R\to\mathbb C$ be a function satisfying, for every real $y$,
--   $$f(y)=y^{1/2-c}\cdot 4\int_0^\infty t^{\,u_1+\mathrm{signShift}(a_1)}e^{-\pi t^2}\,(y/t)^{\,u_2+\mathrm{signShift}(a_2)}e^{-\pi (y/t)^2}\,\frac{dt}{t},$$
--   where `signShift` sends $0\in\mathbb Z/2$ to $0$ and the nonzero class to $1$, so that under the hypotheses $a_1=a_2=0$ the exponents are $u_1$ and $u_2$; all powers are complex powers of the real numbers $y$, $t$ and $y/t$ cast to $\mathbb C$, and the integral is over $t\in(0,\infty)$. The conclusion is threefold: $f$ is differentiable on $(0,\infty)$ as a function of the real variable, its derivative $\operatorname{deriv} f$ is again differentiable on $(0,\infty)$, and for every $y>0$
--   $$y^2 f''(y)+\Bigl(\tfrac14-\nu^2+2\pi k y-4\pi^2y^2\Bigr)f(y)=0,$$
--   with $k=0$ by hypothesis.
--
--   This is the differential equation satisfied at the real place by the weight-zero Whittaker profile attached to the principal parameter $(u_1,a_1,u_2,a_2)$, the multiplicative convolution of two Gaussians normalised by $y^{1/2-c}$; up to the factor $4\sqrt y$ it is Whittaker's (equivalently the modified Bessel) equation for $K_\nu(2\pi y)$. It feeds the identification of the Mellin transform of this profile with the archimedean factor in [`LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero`](thm.html#LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_principal_profile_solves_whittaker_ode.lean

import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.principal_profile_solves_whittaker_ode (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) (ha₁ : a₁ = 0) (ha₂ : a₂ = 0) (c ν : ℂ) (hc : c = (u₁ + u₂) / 2)
    (hν : ν = (u₁ - u₂) / 2) (k : ℝ) (hk : k = 0) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by sorry
