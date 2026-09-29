-- Prove2me | Theorems.Thm_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
-- name    : LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e4cdec79-a8a6-5d7b-ae3d-1891ad414c5f
-- title:
--   Gaussian convolution with shifts (γ,γ+1) is elementary
-- statement:
--   Let $\gamma$ be a complex number and $y$ a real number with $0<y$. The assertion is the identity $$4\int_0^\infty \bigl(t^{\gamma}e^{-\pi t^{2}}\bigr)\bigl((y/t)^{\gamma+1}e^{-\pi (y/t)^{2}}\bigr)\,\frac{dt}{t}\;=\;2\,y^{\gamma}e^{-2\pi y},$$ where the integral is the Bochner integral over the set $\{t\in\mathbb R: t>0\}$ of the complex-valued function of $t$ whose value is the product of the complex power $t^{\gamma}$ of the real number $t$, viewed in $\mathbb C$, with the real exponential $e^{-\pi t^{2}}$, with the complex power $(y/t)^{\gamma+1}$ of the real number $y/t$, and with $e^{-\pi (y/t)^{2}}$, all divided by $t$; on the right-hand side $y^{\gamma}$ is the complex power of the positive real $y$ and $e^{-2\pi y}$ is again a real exponential coerced to $\mathbb C$. Since the right-hand side is nonzero, the identity in particular forces the integrand to be integrable on the positive half-line for every $\gamma$ and every $y>0$.
--
--   Written multiplicatively, the left-hand side is the multiplicative convolution of the two weighted Gaussians $t\mapsto t^{\gamma}e^{-\pi t^{2}}$ and $t\mapsto t^{\gamma+1}e^{-\pi t^{2}}$, i.e. the archimedean torus profile whose Mellin transform is $\Gamma_{\mathbb R}(s+\gamma)\Gamma_{\mathbb R}(s+\gamma+1)=\Gamma_{\mathbb C}(s+\gamma)$; the identity is the classical evaluation $\int_0^\infty e^{-a t^{2}-b/t^{2}}\,dt=\tfrac12\sqrt{\pi/a}\,e^{-2\sqrt{ab}}$, equivalently the closed form $K_{1/2}(z)=\sqrt{\pi/(2z)}\,e^{-z}$ for the Macdonald function. It is used in the Langlands–Tunnell part of the development, in the computation of archimedean gamma factors for Rankin–Selberg integrals and in the cubic-induction and converse-theorem steps that compare principal-series and discrete-series profiles at a real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul.lean

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
    (γ : ℂ) (y : ℝ) (hy : 0 < y) :
    (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ γ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
      = 2 * ((y : ℂ) ^ γ * (Real.exp (-(2 * Real.pi * y)) : ℂ)) := by sorry
