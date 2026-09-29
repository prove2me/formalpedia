-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp
-- name    : LanglandsTunnell.norm_mulConvGaussian_le_rpow_max_mul_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e0c8a90d-e4a5-5d0a-ba6a-ee2ee2e08e10
-- title:
--   Exponential decay of the Gaussian multiplicative convolution
-- statement:
--   Let $u_1,u_2\in\mathbb{C}$ and let $a_1,a_2\in\mathbb{Z}/2$; write $\sigma(a)=0$ if $a=0$ and $\sigma(a)=1$ otherwise, so that the two exponents are $\alpha=u_1+\sigma(a_1)$ and $\beta=u_2+\sigma(a_2)$, viewed as complex numbers. The assertion is the existence of a real constant $C$ (allowed to depend on $u_1,a_1,u_2,a_2$) such that for every real $y\ge 1$,
--   $$\Bigl\| 4\int_{(0,\infty)} \bigl(t^{\alpha}e^{-\pi t^2}\bigr)\bigl((y/t)^{\beta}e^{-\pi (y/t)^2}\bigr)\,\frac{dt}{t}\Bigr\| \;\le\; C\, y^{\max(\operatorname{Re}\alpha,\ \operatorname{Re}\beta)}\, e^{-\pi y},$$
--   where the integral is the Bochner integral over $\mathrm{Ioi}\,0$ of the indicated $\mathbb{C}$-valued function of $t$, the complex powers are those of the coercions of the positive reals $t$ and $y/t$ to $\mathbb{C}$, the Gaussian factors are real exponentials coerced to $\mathbb{C}$, and the division by $t$ is in $\mathbb{C}$. On the right-hand side $y$ is raised to a real power. No hypothesis is placed on $u_1,u_2$ beyond membership in $\mathbb{C}$; the conclusion is uniform in $y\ge 1$ only, nothing being claimed for $0<y<1$.
--
--   This is the decay estimate at infinity for the archimedean Whittaker profile attached to a principal-series parameter, namely four times the multiplicative convolution of the two weighted Gaussians $t\mapsto t^{\alpha}e^{-\pi t^2}$ and $t\mapsto t^{\beta}e^{-\pi t^2}$; the rate $e^{-\pi y}$ is not optimal but suffices. It is used to justify absolute convergence of the Mellin transform of this profile in the identification of the archimedean factor, being cited in the weight-one and weight-zero Mellin-identity statements for solutions of the Whittaker ordinary differential equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp.lean

import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_mulConvGaussian_le_rpow_max_mul_exp (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖(4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖
        ≤ C * y ^ (max (u₁ + signShift a₁).re (u₂ + signShift a₂).re) * Real.exp (-(π * y)) := by sorry
