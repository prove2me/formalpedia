-- Prove2me | Theorems.Thm_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided
-- name    : LanglandsTunnell.integrable_dualFibres_of_integrable_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/82da16ed-ea45-5a22-8c8c-820954e183bc
-- title:
--   Integrability transport through the dual fibre maps
-- statement:
--   Fix $A_1,\beta,\gamma,w\in\mathbb{C}$, natural numbers $m,n$, a measurable function $S:\mathbb{R}\to\mathbb{C}$ which is invariant under positive rescaling, i.e. $S(y/c)=S(y)$ for all $c>0$ and all $y\in\mathbb{R}$, and a measurable $g:\mathbb{R}\to\mathbb{C}$. Assume two integrability hypotheses for functions of $(x_1,x_2,x_3,x_4)\in\mathbb{R}^4$ with respect to the product of Lebesgue measure restricted to $(0,\infty)$, to $(-\infty,0)$, to $(0,\infty)$, and unrestricted Lebesgue measure in the last variable: the integrand $x_1^{A_1-\gamma-1}e^{-2\pi x_1}|x_2|^{-\gamma-2}x_3^{\,n-w-\beta-3}\exp\bigl(-\pi(x_2^{-2}+x_1^2x_2^2+x_3^{-2})\bigr)$ times $g(-x_1|x_2|/x_3)$ times $\bigl((x_2^{-1}-x_3^{-1}+x_1x_2)+iz\bigr)^m e^{-\pi x_4^2}$ with $z=x_4$ (hypothesis `hminus`), and the variant with $g(x_1|x_2|/x_3)$ in place of $g(-x_1|x_2|/x_3)$ and with the bracket $\bigl((-x_2^{-1}-x_3^{-1}-x_1x_2)+ix_4\bigr)^m$ (hypothesis `hplus`). The conclusion is the conjunction of two statements about the three-variable kernel obtained by integrating the Gaussian factor in $z$: first, that $(q_1,q_2,q_3)\mapsto |q_3|^{w+1}\,|q_1|^{A_1}e^{-2\pi|q_1|}(q_3^{-1})^n S(q_3)|q_3|^{\beta}q_2^{\gamma}\exp\bigl(-\pi(q_2^{-2}+q_1^2q_2^2+q_3^2)\bigr)g(q_3/q_2)\int_{\mathbb{R}}\bigl((q_1q_2-q_2^{-1}+q_3)+iz\bigr)^m e^{-\pi z^2}\,dz$ is integrable for the product of Lebesgue measure restricted to $(-\infty,0)$, to $(0,\infty)$, and unrestricted; and second, the same assertion with the roles of the last two coordinates interchanged throughout, integrable for the product of Lebesgue measure restricted to $(-\infty,0)$, unrestricted, and restricted to $(0,\infty)$.
--
--   This is the integrability companion of the change-of-variables identity that rewrites the dual fibre integrals of the Rankin–Selberg computation as one-sided four-variable integrals: it converts integrability on the four-variable side (flat and mirrored brackets) into integrability of the three-variable kernel weighted by $|u|^{w+1}$, in both coordinate orders used later. It feeds the Fubini and Gamma-factor steps in the construction of the dual torus pair expansion within the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrable_dualFibres_of_integrable_oneSided
    (A₁ β γ w : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (hSm : Measurable S) (g : ℝ → ℂ) (hg : Measurable g)
    (hminus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          (fun v : ℝ => g (-v)) (x.1 * |x.2.1| / x.2.2.1) *
          ((((x.2.1⁻¹ - x.2.2.1⁻¹ + x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))))
    (hplus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          ((((-x.2.1⁻¹ - x.2.2.1⁻¹ - x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
            g (q.2.2 / q.2.1) *
            (∫ z : ℝ, (((q.1 * q.2.1 - q.2.1⁻¹ + q.2.2 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ))) ∧
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.2 ^ 2)⁻¹ + q.1 ^ 2 * q.2.2 ^ 2 + q.2.1 ^ 2))) : ℂ) *
            g (q.2.1 / q.2.2) *
            (∫ z : ℝ, (((q.1 * q.2.2 - q.2.2⁻¹ + q.2.1 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))) := by sorry
