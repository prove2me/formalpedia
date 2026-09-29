-- Prove2me | Theorems.Thm_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
-- name    : LanglandsTunnell.integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/5b591fe2-c373-5523-aebd-2ad0a9aad381
-- title:
--   Integrability of the Gaussian–Mellin factor against |u|^{w+1}K
-- statement:
--   Let $w\in\mathbb C$ satisfy $-1<\operatorname{Re}w$, and let $K:\mathbb R\to\mathbb R\to\mathbb R\to\mathbb C$ be such that the uncurried map $(t,u,Y)\mapsto K(t,u,Y)$ on $\mathbb R\times\mathbb R\times\mathbb R$ is measurable. Assume that the function $(t,u,Y)\mapsto (|u|)^{w+1}K(t,u,Y)$, the power being the complex power of the real number $|u|$, is integrable for the product of Lebesgue measure restricted to $(-\infty,0)$ in $t$, Lebesgue measure on $\mathbb R$ in $u$, and Lebesgue measure restricted to $(0,\infty)$ in $Y$. The conclusion is that the function of four real variables
--   $$(a,t,u,Y)\ \longmapsto\ a^{w}\,\exp\bigl(-\pi\,a^{2}(u^{2})^{-1}\bigr)\,K(t,u,Y),$$
--   with $a^{w}$ the complex power of the real number $a$ and the exponential a real number viewed in $\mathbb C$, is integrable for the product of Lebesgue measure restricted to $(0,\infty)$ in $a$, Lebesgue measure restricted to $(-\infty,0)$ in $t$, Lebesgue measure on $\mathbb R$ in $u$, and Lebesgue measure restricted to $(0,\infty)$ in $Y$.
--
--   This is the Fubini–Tonelli step that adjoins the outer Gaussian–Mellin variable $a$ to an already integrable three-variable kernel, the price of the extra variable being one unit of growth in $|u|$. It feeds the integrability hypothesis used in the Rankin–Selberg computation of the Whittaker-type integral for a discrete series contribution, namely [`LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
    (w : ℂ) (hw : -1 < w.re) (K : ℝ → ℝ → ℝ → ℂ)
    (hK : Measurable fun p : ℝ × ℝ × ℝ => K p.1 p.2.1 p.2.2)
    (h3 : Integrable (fun q : ℝ × ℝ × ℝ => ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) * K q.1 q.2.1 q.2.2)
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
        ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))))) := by sorry
