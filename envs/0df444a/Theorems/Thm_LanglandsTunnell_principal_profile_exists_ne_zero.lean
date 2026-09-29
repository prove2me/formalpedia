-- Prove2me | Theorems.Thm_LanglandsTunnell_principal_profile_exists_ne_zero
-- name    : LanglandsTunnell.principal_profile_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/037654c8-09fb-5eb0-b3bf-7cb985014b9c
-- title:
--   Non-vanishing of the principal-series archimedean profile
-- statement:
--   Let $u_1,u_2,c$ be complex numbers and $a_1,a_2\in\mathbb{Z}/2$, and write $\alpha=u_1+\mathrm{signShift}(a_1)$, $\beta=u_2+\mathrm{signShift}(a_2)$, where `signShift` sends $0$ to $0$ and the nonzero class to $1$. Let $f\colon\mathbb{R}\to\mathbb{C}$ be a function subject to the hypothesis that for every real $y$ (not only for $y>0$) $$f(y)=y^{1/2-c}\cdot\Bigl(4\int_{t\in(0,\infty)}\bigl(t^{\alpha}e^{-\pi t^{2}}\bigr)\bigl((y/t)^{\beta}e^{-\pi (y/t)^{2}}\bigr)\frac{dt}{t}\Bigr),$$ all powers being complex powers of the real bases cast to $\mathbb{C}$, and the integral being the Bochner integral over $(0,\infty)$ with respect to Lebesgue measure (so equal to $0$ whenever the integrand is not integrable). The conclusion is that there exists a real $y$ with $0<y$ and $f(y)\neq 0$. Thus the assertion is the existential non-vanishing of the normalised multiplicative convolution of the two weighted Gaussians on the positive reals, not a pointwise statement about all $y>0$.
--
--   This is the non-degeneracy statement for the archimedean Whittaker profile attached to a principal parameter $(u_1,a_1,u_2,a_2)$: the profile whose Mellin transform is the corresponding product of two $\Gamma_{\mathbb{R}}$-factors is not identically zero on $(0,\infty)$. It is used to supply the non-vanishing side condition in the construction of Whittaker profiles realising a prescribed archimedean factor, in the weight-one and weight-zero cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_principal_profile_exists_ne_zero.lean

import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.principal_profile_exists_ne_zero (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (c : ℂ) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    ∃ y : ℝ, 0 < y ∧ f y ≠ 0 := by sorry
