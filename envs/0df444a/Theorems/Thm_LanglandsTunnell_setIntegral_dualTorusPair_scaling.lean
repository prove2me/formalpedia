-- Prove2me | Theorems.Thm_LanglandsTunnell_setIntegral_dualTorusPair_scaling
-- name    : LanglandsTunnell.setIntegral_dualTorusPair_scaling
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c7191290-6c28-5ddf-9c63-85a9bcd79461
-- title:
--   Dual torus-pair scaling identity for the inner integrals
-- statement:
--   Let $A_1,A_2,\beta,\gamma$ be complex numbers, $m,n$ natural numbers, $S,g:\mathbb R\to\mathbb C$ arbitrary functions, and assume $S$ is invariant under positive dilations, i.e. $S(y/c)=S(y)$ for all $c>0$ and all $y\in\mathbb R$. Then the two following iterated Bochner integrals are equal. The first is $\int_{a_2>0}\int_{a_1<0}|a_1|^{A_1}a_2^{A_2}e^{-2\pi|a_1|/a_2}\Big(\int_{y_1\in\mathbb R}\int_{y_2>0}(y_1^{-1})^n S(y_1)|y_1|^{\beta}y_2^{\gamma}e^{-\pi((a_2y_2)^{-2}+y_1^{-2}+a_1^2y_2^2+a_2^2y_1^2)}g(y_1/y_2)I(a_1y_2-(a_2y_2)^{-1}+a_2y_1)\Big)$, and the second is $\int_{a_2>0}\int_{t<0}\int_{u\in\mathbb R}\int_{Y>0}a_2^{A_1+A_2+n-\beta-\gamma-1}e^{-\pi a_2^2/u^2}\cdot|t|^{A_1}e^{-2\pi|t|}(u^{-1})^nS(u)|u|^{\beta}Y^{\gamma}e^{-\pi(Y^{-2}+t^2Y^2+u^2)}g(u/Y)I(tY-Y^{-1}+u)$, where in both cases $I(w)=\int_{z\in\mathbb R}(w+iz)^m e^{-\pi z^2}\,dz$; here real powers with complex exponents are the complex power $x^A$ of the real base, and $a_2^{n}$ occurs as the natural-number power $n$ inside the exponent $A_1+A_2+n-\beta-\gamma-1$. No integrability or measurability hypothesis is imposed, the identity being an equality of Bochner integrals with the usual convention that a non-integrable integral has value $0$.
--
--   The identity records the effect of the substitutions $a_1=a_2t$, $y_1=u/a_2$, $y_2=a_2^{-1}Y$ carried out at fixed $a_2>0$ inside the unfolded dual torus-pair integral, after which every factor except $a_2^{A_1+A_2+n-\beta-\gamma-1}e^{-\pi a_2^2/u^2}$ is free of $a_2$. It is used in the evaluation of the dual archimedean Rankin–Selberg torus-pair integral, namely by [`LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_setIntegral_dualTorusPair_scaling.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_dualTorusPair_scaling
    (A₁ A₂ β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (g : ℝ → ℂ) :
    (∫ a₂ in Ioi (0 : ℝ), ∫ a₁ in Iio (0 : ℝ),
        ((|a₁| : ℝ) : ℂ) ^ A₁ * ((a₂ : ℝ) : ℂ) ^ A₂ * (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
        ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ),
          ((y₁⁻¹ : ℝ) : ℂ) ^ n * S y₁ * ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
            g (y₁ / y₂) *
            (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
      = ∫ a₂ in Ioi (0 : ℝ), ∫ t in Iio (0 : ℝ), ∫ u : ℝ, ∫ Y in Ioi (0 : ℝ),
          ((a₂ : ℝ) : ℂ) ^ (A₁ + A₂ + (n : ℂ) - β - γ - 1) * (Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) : ℂ) *
          (((|t| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * S u * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            g (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by sorry
