-- Prove2me | Theorems.Thm_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
-- name    : LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/36a48f3d-b242-5510-b0cb-fd4f5b8b285e
-- title:
--   Integrability of a Gaussian–hyperbolic integrand on σ w>v
-- statement:
--   Let $a\in\mathbb{C}$ satisfy $\operatorname{Re} a>-1$, let $k\in\mathbb{Z}$, $n\in\mathbb{N}$, and let $v\in\mathbb{R}$ with $v>0$. Consider the function on $\mathbb{R}\times\mathbb{R}$ sending $q=(\sigma,w)$ to
--   $$(\sigma w-v)^{a}\,w^{k}\,e^{-\pi(\sigma^{2}+w^{2})}\cdot\int_{\mathbb{R}}(\sigma-iz)^{n}e^{-\pi z^{2}}\,dz,$$
--   where the real numbers $\sigma w-v$ and $w$ are regarded as complex numbers and raised to the complex power $a$ and the integer power $k$ respectively by the principal branch used in Mathlib, the Gaussian factor is the real exponential viewed in $\mathbb{C}$, and the last factor is the Bochner integral over $z\in\mathbb{R}$ of the stated complex-valued function. The assertion is that this function is integrable, with respect to Lebesgue measure on the plane, on the open region $\{(\sigma,w):0<\sigma,\ 0<w,\ v<\sigma w\}$, i.e. the restriction of the measure to that set makes it integrable.
--
--   This is the integrability input needed to evaluate, by Fubini and a change of variables, the double integral of $(\sigma w-v)^{a}w^{k}e^{-\pi(\sigma^{2}+w^{2})}$ against a Gaussian moment over the hyperbolic region; the final factor is the $n$-th Gaussian moment polynomial in $\sigma$, which the cited identity expresses through iterated derivatives of $s\mapsto e^{-\pi s^{2}}$. It is used in the computation of the archimedean integral identifying such an integral with a Gamma factor times an evaluation of a homogeneous polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion.lean

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
    (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
          (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
          ∫ z : ℝ, ((q.1 : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} := by sorry
