-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
-- name    : LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/6308709d-42d3-52e2-8b80-8a5596c9e779
-- title:
--   Torus–Gauss integral of two Gaussian convolutions in Euler form
-- statement:
--   Let $p_1,p_2,q_1,q_2,\alpha,\beta,\gamma$ be complex numbers subject to eight positivity conditions on real parts: $\operatorname{Re}(\alpha-\beta+p_1)>0$, $\operatorname{Re}(\alpha-\beta+p_2)>0$, $\operatorname{Re}(q_1-\gamma-1)>0$, $\operatorname{Re}(q_2-\gamma-1)>0$, and $\operatorname{Re}(\alpha+1+p_i+q_j)>0$ for all $i,j\in\{1,2\}$. Write $G_{a,b}(u)=4\int_0^\infty u'^{\,}\!$-free Gaussian convolution profile $G_{a,b}(u)=4\int_0^\infty r^{a}e^{-\pi r^{2}}\,(u/r)^{b}e^{-\pi (u/r)^{2}}\,\frac{dr}{r}$, all powers being complex powers of the real positive bases. The assertion is the equality of iterated integrals over $(0,\infty)$ in the variables $t$, $y_1$, $y_2$ (in that order, innermost $y_2$):
--   $$\int_0^\infty\!\!\int_0^\infty\!\!\int_0^\infty G_{p_1,p_2}(t)\,t^{\alpha}\,G_{q_1,q_2}\!\Big(\frac{t y_1}{y_2}\Big)\,y_1^{\beta}y_2^{\gamma}\,e^{-\pi/y_1^{2}}e^{-\pi t^{2}y_1^{2}}e^{-\pi/y_2^{2}}$$
--   $$=\tfrac12\,\Gamma_{\mathbb R}(\alpha-\beta+p_2)\,\Gamma_{\mathbb R}(q_2-\gamma-1)\,\Gamma_{\mathbb R}(\alpha+1+p_1+q_1)\int_0^\infty\!\!\int_0^\infty x^{\frac{\alpha-\beta+p_1}{2}-1}(1+x)^{-\frac{\alpha-\beta+p_2}{2}}y^{\frac{q_1-\gamma-1}{2}-1}(1+y)^{-\frac{q_2-\gamma-1}{2}}(1+x+y)^{-\frac{\alpha+1+p_1+q_1}{2}},$$
--   with $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ as in `Complex.Gammaℝ`, the outer variable on the right being $x$. No balance relation among $\alpha,\beta,\gamma,p_i,q_j$ is assumed.
--
--   This is the reduction of an archimedean torus integral against two Gaussian-convolution profiles — those whose Mellin transforms are products $\Gamma_{\mathbb R}(s+a)\Gamma_{\mathbb R}(s+b)$ — to a double Euler (Barnes-type) integral over the positive quadrant, with three $\Gamma_{\mathbb R}$-factors extracted. It serves the archimedean computations in the Langlands–Tunnell part of the development, and is used by [`LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div`](thm.html#LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div); the beta-integral evaluation [`Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div`](thm.html#Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div) enters the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_mul_integral_Ioi_integral_Ioi_cpow
    (p₁ p₂ q₁ q₂ α β γ : ℂ)
    (hp₁ : 0 < (α - β + p₁).re) (hp₂ : 0 < (α - β + p₂).re)
    (hq₁ : 0 < (q₁ - γ - 1).re) (hq₂ : 0 < (q₂ - γ - 1).re)
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
          (Complex.Gammaℝ (α - β + p₂) * Complex.Gammaℝ (q₂ - γ - 1) * Complex.Gammaℝ (α + 1 + p₁ + q₁)) *
          ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
            (x : ℂ) ^ ((α - β + p₁) / 2 - 1) * ((1 + x : ℝ) : ℂ) ^ (-((α - β + p₂) / 2)) *
              ((y : ℂ) ^ ((q₁ - γ - 1) / 2 - 1) * ((1 + y : ℝ) : ℂ) ^ (-((q₂ - γ - 1) / 2))) *
              ((1 + x + y : ℝ) : ℂ) ^ (-((α + 1 + p₁ + q₁) / 2)) := by sorry
