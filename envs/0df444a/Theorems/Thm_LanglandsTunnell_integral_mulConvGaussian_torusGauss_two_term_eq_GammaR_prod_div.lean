-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
-- name    : LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0dfa6087-844e-5b23-9930-3005bb62a7a6
-- title:
--   Two-term contiguity identity for a Gaussian torus triple integral
-- statement:
--   For complex parameters $\pi_1,\pi_2,q_1,q_2,\alpha,\beta,\gamma$, write $G_{p_1,p_2}(u)=4\int_0^\infty r^{p_1}e^{-\pi r^2}\,(u/r)^{p_2}e^{-\pi (u/r)^2}\,\frac{dr}{r}$ for the multiplicative convolution of two Gaussians with power weights (all powers being complex powers of positive reals), and for a profile $\phi$ put $J(\phi;\alpha,\beta,\gamma)=\int_0^\infty\!\int_0^\infty\!\int_0^\infty \phi(t)\,t^{\alpha}\,G_{q_1,q_2}(ty_1/y_2)\,y_1^{\beta}y_2^{\gamma}\,e^{-\pi/y_1^2}e^{-\pi t^2y_1^2}e^{-\pi/y_2^2}\,dy_2\,dy_1\,dt$, all integrals being Bochner integrals over $(0,\infty)$. Assume the balance relation $\beta-\gamma=2\alpha+2+\pi_1+\pi_2$, together with the six positivity conditions $\operatorname{Re}(\alpha-\beta+\pi_1+1)>0$, $\operatorname{Re}(\alpha-\beta+\pi_2)>0$, $\operatorname{Re}(\alpha+1+\pi_1+q_j)>0$ and $\operatorname{Re}(\alpha+2+\pi_2+q_j)>0$ for $j=1,2$. Then
--   $$J\bigl(G_{\pi_1,\pi_2+1};\alpha,\beta-1,\gamma\bigr)+J\bigl(G_{\pi_1+1,\pi_2};\alpha+1,\beta+1,\gamma\bigr)=\frac12\cdot\frac{\Gamma_{\mathbb R}(\alpha-\beta+\pi_1+1)\,\Gamma_{\mathbb R}(\alpha-\beta+\pi_2)\prod_{j=1}^{2}\Gamma_{\mathbb R}(\alpha+1+\pi_1+q_j)\,\Gamma_{\mathbb R}(\alpha+2+\pi_2+q_j)}{\Gamma_{\mathbb R}(\beta-\gamma+q_1+q_2+1)},$$
--   where $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ is `Complex.Gammaℝ`. No separate positivity hypotheses on $q_1-\gamma-1$, $q_2-\gamma-1$ are imposed.
--
--   This is a contiguity relation in the Barnes family of two-variable beta-type integrals: neither of the two triple integrals is individually of the closed product form, but the balance condition makes their sum collapse to a ratio of archimedean Gamma factors. It is used in the archimedean computations of the Langlands–Tunnell converse-theorem step, where the corresponding torus integrals with twisted Gaussian profiles are evaluated as products of $\Gamma_{\mathbb R}$-factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
    (π₁ π₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + π₁ + π₂)
    (hp₁ : 0 < (α - β + π₁ + 1).re) (hp₂ : 0 < (α - β + π₂).re)
    (h₁₁ : 0 < (α + 1 + π₁ + q₁).re) (h₁₂ : 0 < (α + 1 + π₁ + q₂).re)
    (h₂₁ : 0 < (α + 2 + π₂ + q₁).re) (h₂₂ : 0 < (α + 2 + π₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β - 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) +
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α + 1) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β + 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + π₁ + 1) * Complex.Gammaℝ (α - β + π₂) *
            (Complex.Gammaℝ (α + 1 + π₁ + q₁) * Complex.Gammaℝ (α + 1 + π₁ + q₂) *
              Complex.Gammaℝ (α + 2 + π₂ + q₁) * Complex.Gammaℝ (α + 2 + π₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂ + 1) := by sorry
