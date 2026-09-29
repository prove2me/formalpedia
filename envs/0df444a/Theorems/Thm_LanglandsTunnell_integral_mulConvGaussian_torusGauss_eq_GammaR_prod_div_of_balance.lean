-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
-- name    : LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/fbaea607-1f6e-54ab-885b-3855ac18452c
-- title:
--   A torus--Gauss triple integral as a ratio of Γ_ℝ-products
-- statement:
--   Fix complex numbers $p_1,p_2,q_1,q_2,\alpha,\beta,\gamma$ subject to the balance relation $\beta-\gamma=2\alpha+2+p_1+p_2$ and to the positivity conditions $\operatorname{Re}(\alpha-\beta+p_1)>0$, $\operatorname{Re}(\alpha-\beta+p_2)>0$ and $\operatorname{Re}(\alpha+1+p_i+q_j)>0$ for $i,j\in\{1,2\}$. Write $G_{a,b}(y)=4\int_0^\infty r^{a}e^{-\pi r^2}\,(y/r)^{b}e^{-\pi (y/r)^2}\,\frac{dr}{r}$ for the multiplicative Gaussian convolution appearing in the integrand, with complex powers of the positive reals $r$ and $y/r$ taken as principal values. Then the iterated Bochner integral over $t\in(0,\infty)$, $y_1\in(0,\infty)$, $y_2\in(0,\infty)$ (in this order, the $y_2$-integral innermost) of
--   $$G_{p_1,p_2}(t)\,t^{\alpha}\;G_{q_1,q_2}\!\bigl(t y_1/y_2\bigr)\,y_1^{\beta}y_2^{\gamma}\,e^{-\pi/y_1^{2}}e^{-\pi t^{2}y_1^{2}}e^{-\pi/y_2^{2}}$$
--   equals
--   $$\tfrac12\,\frac{\Gamma_{\mathbb R}(\alpha-\beta+p_1)\,\Gamma_{\mathbb R}(\alpha-\beta+p_2)\,\prod_{i,j=1}^{2}\Gamma_{\mathbb R}(\alpha+1+p_i+q_j)}{\Gamma_{\mathbb R}(\beta-\gamma+q_1+q_2)},$$
--   where $\Gamma_{\mathbb R}$ is `Complex.Gammaℝ`. No integrability hypotheses are imposed: the assertion is the stated equality of iterated integrals.
--
--   This is the archimedean closed-form evaluation that reduces the unfolded Rankin–Selberg torus integral for $\mathrm{GL}_2$ to a product of real Gamma factors divided by one more, the profiles $G_{p_1,p_2}$ and $G_{q_1,q_2}$ being the Mellin-theoretic principal-series shapes (with $\Gamma_{\mathbb R}(s+p_1)\Gamma_{\mathbb R}(s+p_2)$ as Mellin transform, degenerating to the discrete-series profile $2y^{q}e^{-2\pi y}$). It is applied in the converse-theorem step, where the gamma factor of the archimedean zeta integral is identified for the various Whittaker profiles, and it rests on the two Beta- and Barnes-type integral evaluations [`Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div`](thm.html#Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div) and [`Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance`](thm.html#Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    (p₁ p₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + p₁ + p₂)
    (hp₁ : 0 < (α - β + p₁).re) (hp₂ : 0 < (α - β + p₂).re)
    (h₁₁ : 0 < (α + 1 + p₁ + q₁).re) (h₁₂ : 0 < (α + 1 + p₁ + q₂).re)
    (h₂₁ : 0 < (α + 1 + p₂ + q₁).re) (h₂₂ : 0 < (α + 1 + p₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ p₂ * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ α *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ q₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ q₂ * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + p₁) * Complex.Gammaℝ (α - β + p₂) *
            (Complex.Gammaℝ (α + 1 + p₁ + q₁) * Complex.Gammaℝ (α + 1 + p₁ + q₂) *
              Complex.Gammaℝ (α + 1 + p₂ + q₁) * Complex.Gammaℝ (α + 1 + p₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂) := by sorry
