-- Prove2me | Theorems.Thm_LanglandsTunnell_setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable
-- name    : LanglandsTunnell.setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/36f1a3f3-ee82-5579-899e-7cb030e5b7e2
-- title:
--   Outer Gaussian–Mellin integration producing the factor Γ_ℝ(w+1)
-- statement:
--   Let $w$ be a complex number with $\operatorname{Re} w > -1$, and let $K : \mathbb R \to \mathbb R \to \mathbb R \to \mathbb C$ be such that the associated function $(t,u,Y) \mapsto K(t,u,Y)$ on $\mathbb R \times \mathbb R \times \mathbb R$ is measurable. Assume further that the four-variable function $(a_2,t,u,Y) \mapsto a_2^{w}\,\exp\bigl(-\pi\,a_2^{2}\,(u^{2})^{-1}\bigr)\,K(t,u,Y)$, with $a_2^w$ the complex power of the real number $a_2$ and the exponential a real exponential viewed in $\mathbb C$, is integrable for the product of Lebesgue measure restricted to $(0,\infty)$ in the variable $a_2$, Lebesgue measure restricted to $(-\infty,0)$ in $t$, Lebesgue measure on all of $\mathbb R$ in $u$, and Lebesgue measure restricted to $(0,\infty)$ in $Y$. Then the iterated integral of that function in the order $a_2$ (over $(0,\infty)$), $t$ (over $(-\infty,0)$), $u$ (over $\mathbb R$), $Y$ (over $(0,\infty)$), read from outermost to innermost, equals $\tfrac12\,\Gamma_{\mathbb R}(w+1)$ times the iterated integral, in the order $t$ over $(-\infty,0)$, then $Y$ over $(0,\infty)$, then $u$ over $\mathbb R$, of $|u|^{w+1}K(t,u,Y)$, where $\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$.
--
--   This is the Gaussian–Mellin (Euler integral) evaluation $\int_0^\infty a^{w}e^{-\pi a^{2}/u^{2}}\,da = \tfrac12 |u|^{w+1}\Gamma_{\mathbb R}(w+1)$ for $u \neq 0$, carried out inside a four-fold integral and accompanied by the reordering of the remaining variables. It is the step that produces the archimedean factor $\Gamma_{\mathbb R}(w+1)$ in the Rankin–Selberg computation of the dual torus integral, and is used in [`LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable
    (w : ℂ) (hw : -1 < w.re) (K : ℝ → ℝ → ℝ → ℂ)
    (hK : Measurable fun p : ℝ × ℝ × ℝ => K p.1 p.2.1 p.2.2)
    (hInt : Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
        ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))))) :
    (∫ a₂ in Ioi (0 : ℝ), ∫ t in Iio (0 : ℝ), ∫ u : ℝ, ∫ Y in Ioi (0 : ℝ),
        ((a₂ : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) : ℂ) * K t u Y)
      = (1 / 2 : ℂ) * Complex.Gammaℝ (w + 1) *
        ∫ t in Iio (0 : ℝ), ∫ Y in Ioi (0 : ℝ), ∫ u : ℝ, ((|u| : ℝ) : ℂ) ^ (w + 1) * K t u Y := by sorry
