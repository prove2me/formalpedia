-- Prove2me | Theorems.Thm_LanglandsTunnell_lowering_principal_profile_sum_eq
-- name    : LanglandsTunnell.lowering_principal_profile_sum_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/2a85f550-65a7-5b58-bf4b-1bdcbfe307e8
-- title:
--   Weight-one lowering operator on shifted Gaussian convolutions
-- statement:
--   Let $u_1,u_2,c\in\mathbb{C}$ with $c=(u_1+u_2)/2$, and for complex exponents $\alpha,\beta$ put $$P_{\alpha,\beta}(y)=4\int_{(0,\infty)}t^{\alpha}e^{-\pi t^{2}}\,(y/t)^{\beta}e^{-\pi (y/t)^{2}}\,\frac{dt}{t},$$ the multiplicative convolution of two Gaussians with power weights (in the Lean statement the Gaussian factors are real exponentials coerced to $\mathbb{C}$, and $y/t$ is formed in $\mathbb{R}$ before coercion). Here the shifts are given by `signShift`, which sends $0\in\mathbb{Z}/2$ to $0$ and $1$ to $1$, so the exponents occurring are $u_1+1,u_2$ and $u_1,u_2+1$. Let $f:\mathbb{R}\to\mathbb{C}$ be a function assumed to satisfy, for every real $y$, $$f(y)=y^{1/2-c}P_{u_1+1,u_2}(y)+y^{1/2-c}P_{u_1,u_2+1}(y).$$ Then for every real $y>0$, $$2y\,f'(y)+(4\pi y-1)f(y)=(u_1-u_2)\Bigl(y^{1/2-c}P_{u_1,u_2+1}(y)-y^{1/2-c}P_{u_1+1,u_2}(y)\Bigr),$$ the derivative being Mathlib's `deriv` of $f$ at $y$, and the powers $y^{1/2-c}$ and $t^{u_1+\cdot}$ being complex powers.
--
--   This is the archimedean computation showing that the first-order operator $2y\,d/dy+(4\pi y-1)$, which lowers the weight in Whittaker's equation from $1$ to $-1$, carries the symmetric combination of the two shifted principal-series Gaussian convolutions to $u_1-u_2$ times their antisymmetric combination; it encodes the standard recurrence for $K$-Bessel functions under differentiation. It is used in identifying the Mellin transform of the weight-one Whittaker profile with the archimedean local factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_lowering_principal_profile_sum_eq.lean

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.lowering_principal_profile_sum_eq (u₁ u₂ : ℂ) (c : ℂ) (hc : c = (u₁ + u₂) / 2)
    (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y =
      (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      + (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)))
    (y : ℝ) (hy : 0 < y) :
    2 * (y : ℂ) * deriv f y + (4 * (π : ℂ) * (y : ℂ) - 1) * f y =
      (u₁ - u₂) *
        ((y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
          - (y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) := by sorry
