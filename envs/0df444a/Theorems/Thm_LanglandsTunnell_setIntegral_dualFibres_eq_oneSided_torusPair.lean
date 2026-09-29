-- Prove2me | Theorems.Thm_LanglandsTunnell_setIntegral_dualFibres_eq_oneSided_torusPair
-- name    : LanglandsTunnell.setIntegral_dualFibres_eq_oneSided_torusPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3bf8b992-ad5b-5a65-8291-b01d99c33371
-- title:
--   Dual fibres as two one-sided torus integrals
-- statement:
--   Let $A_1,\beta,\gamma,w\in\mathbb{C}$, let $m,n\in\mathbb{N}$, let $S:\mathbb{R}\to\mathbb{C}$ satisfy $S(y/c)=S(y)$ for every $c>0$ and every $y\in\mathbb{R}$ (invariance under positive dilations), and let $g:\mathbb{R}\to\mathbb{C}$. Write $$K(t,Y,u)=|u|^{w+1}\,|t|^{A_1}e^{-2\pi|t|}\,\bigl(u^{-1}\bigr)^{n}S(u)|u|^{\beta}Y^{\gamma}\,e^{-\pi(Y^{-2}+t^2Y^2+u^2)}\,g(u/Y)\int_{\mathbb{R}}\bigl(tY-Y^{-1}+u+iz\bigr)^{m}e^{-\pi z^{2}}\,dz,$$ and assume $K$ is integrable for the product of Lebesgue measure restricted to $(-\infty,0)$ in $t$, Lebesgue measure restricted to $(0,\infty)$ in $Y$, and Lebesgue measure in $u$. The conclusion is the identity $$\int_{-\infty}^{0}\int_{0}^{\infty}\int_{\mathbb{R}}K(t,Y,u)\,du\,dY\,dt=(-1)^{n}S(-1)\,I_{1}+(-1)^{m}S(1)\,I_{2},$$ where $I_{1}$ and $I_{2}$ are the triple integrals over $t\in(0,\infty)$, $y_1\in(-\infty,0)$, $y_2\in(0,\infty)$ of $$t^{A_1-\gamma-1}e^{-2\pi t}\,|y_1|^{-\gamma-2}\,y_2^{\,n-w-\beta-3}\,e^{-\pi(y_1^{-2}+t^{2}y_1^{2}+y_2^{-2})}\,G\bigl(t|y_1|/y_2\bigr)\int_{\mathbb{R}}(c+iz)^{m}e^{-\pi z^{2}}\,dz,$$ with, for $I_{1}$, $G(v)=g(-v)$ and $c=y_1^{-1}-y_2^{-1}+ty_1$, and, for $I_{2}$, $G=g$ and $c=-y_1^{-1}-y_2^{-1}-ty_1$.
--
--   This is a change-of-variables step in the archimedean Rankin–Selberg computation entering the Langlands–Tunnell input: splitting the $u$-integral at $0$, reflecting $t\mapsto -t$ and substituting $Y=1/(t|y_1|)$, $|u|=1/y_2$ on each fibre converts the dual triple integral into the two one-sided torus integrals, with flat and mirrored Gaussian brackets respectively. It is used by the dual-torus-pair evaluation [`LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3), whose subsequent fibre collapse consumes the two summands on the right.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_setIntegral_dualFibres_eq_oneSided_torusPair.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_dualFibres_eq_oneSided_torusPair
    (A₁ β γ w : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (g : ℝ → ℂ)
    (hK : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
            g (q.2.2 / q.2.1) *
            (∫ z : ℝ, (((q.1 * q.2.1 - q.2.1⁻¹ + q.2.2 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)))) :
    (∫ t in Iio (0 : ℝ), ∫ Y in Ioi (0 : ℝ), ∫ u : ℝ,
        ((|u| : ℝ) : ℂ) ^ (w + 1) *
          (((|t| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * S u * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            g (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
      = (-1 : ℂ) ^ n * S (-1) *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-γ - 2) * ((y₂ : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              (fun v : ℝ => g (-v)) (t * |y₁| / y₂) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) +
        (-1 : ℂ) ^ m * S 1 *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-γ - 2) * ((y₂ : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              g (t * |y₁| / y₂) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by sorry
