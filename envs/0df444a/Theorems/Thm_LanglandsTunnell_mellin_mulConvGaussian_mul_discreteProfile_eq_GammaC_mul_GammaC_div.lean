-- Prove2me | Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
-- name    : LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/bd4a272e-49ee-56f4-be9e-7421139f0642
-- title:
--   Mellin transform of Gaussian convolution times discrete profile
-- statement:
--   Let $\alpha,\beta,u,s$ be complex numbers and $k$ a natural number with $1\le k$, and assume $\operatorname{Re}(s+\alpha+u+k/2)>0$ and $\operatorname{Re}(s+\beta+u+k/2)>0$. Consider the function on $\mathbb{R}$ given by
--   $$y\;\longmapsto\;\Bigl(4\int_{t>0} t^{\alpha}e^{-\pi t^{2}}\,(y/t)^{\beta}e^{-\pi (y/t)^{2}}\,\frac{dt}{t}\Bigr)\cdot\Bigl(2\,y^{u+k/2}e^{-2\pi y}\Bigr),$$
--   where the $t$-integral is the Lebesgue integral over $\mathrm{Ioi}\,0$ of the indicated complex-valued integrand (real powers of $t$ and of $y/t$ being taken via the complex power with real base, and the Gaussian factors being real exponentials coerced to $\mathbb{C}$), and the second factor is the scalar multiple $2\cdot y^{u+k/2}\cdot e^{-2\pi y}$. The theorem asserts two things simultaneously: first, `MellinConvergent` holds for this function at $s$, i.e. $y\mapsto y^{s-1}$ times the function is integrable on $(0,\infty)$; and second, its Mellin transform at $s$ equals
--   $$2\,\frac{\Gamma_{\mathbb{C}}(s+\alpha+u+\tfrac{k}{2})\,\Gamma_{\mathbb{C}}(s+\beta+u+\tfrac{k}{2})}{\Gamma_{\mathbb{R}}(2s+\alpha+\beta+2u+k+1)},$$
--   with $\Gamma_{\mathbb{R}}$ and $\Gamma_{\mathbb{C}}$ the completed gamma factors of Mathlib.
--
--   This is the principal-series-times-discrete-series case of the archimedean Rankin integral: the multiplicative Gaussian convolution $G_{\alpha,\beta}$, whose own Mellin transform is $\Gamma_{\mathbb{R}}(s+\alpha)\Gamma_{\mathbb{R}}(s+\beta)$, is paired against the profile $2y^{u+k/2}e^{-2\pi y}$, whose Mellin transform is $\Gamma_{\mathbb{C}}(s+u+k/2)$; classically it is the integral $\int_0^{\infty}x^{\mu-1}e^{-x}K_{\nu}(x)\,dx$ evaluated by a beta integral. It feeds the computation [`LanglandsTunnell.setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR`](thm.html#LanglandsTunnell.setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR), and its proof invokes the convergence and evaluation of the beta integral $\int_0^{\infty}q^{b-1}(1+q)^{-(a+b)}\,dq$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
    (α β u s : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (h₁ : 0 < (s + α + u + (k : ℂ) / 2).re) (h₂ : 0 < (s + β + u + (k : ℂ) / 2).re) :
    MellinConvergent (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s ∧
    mellin (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s
      = 2 * (Complex.Gammaℂ (s + α + u + (k : ℂ) / 2) * Complex.Gammaℂ (s + β + u + (k : ℂ) / 2)) /
        Complex.Gammaℝ (2 * s + α + β + 2 * u + (k : ℂ) + 1) := by sorry
