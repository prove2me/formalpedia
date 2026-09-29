-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
-- name    : LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/998822f7-e489-5cee-a98a-121a2ba2ed03
-- title:
--   Second integral representation of the Bessel kernel
-- statement:
--   Let $\nu$ be a complex number and $x$ a real number with $0 < x$. The Bessel kernel is defined by $\mathrm{besselKernel}\,\nu\,x = \int_{(0,\infty)} e^{-x(t+t^{-1})/2}\, t^{\nu-1}\,dt$, the Bochner integral over the interval $\mathrm{Ioi}\,0$ of the $\mathbb{C}$-valued function whose value at $t$ is the real exponential $e^{-x(t+t^{-1})/2}$, viewed as a complex number, times the complex power $t^{\nu-1}$ of the coercion of $t$. The assertion is the identity $$\mathrm{besselKernel}\,\nu\,x = (2/x)^{\nu}\int_{(0,\infty)} e^{-(\tau + x^2/(4\tau))}\,\tau^{\nu-1}\,d\tau,$$ where $(2/x)^{\nu}$ is the complex power of the coercion of the real number $2/x$, and the integrand on the right is again the coercion of the real exponential $e^{-(\tau + x^{2}/(4\tau))}$ times the complex power $\tau^{\nu-1}$. No integrability hypothesis is imposed: both sides are Bochner integrals over $(0,\infty)$ with respect to Lebesgue measure, and the equality holds as stated for every complex $\nu$ and every positive real $x$.
--
--   This is the classical second integral representation of the Bessel function of imaginary argument (Watson, §6.22), normalised so that $\mathrm{besselKernel}$ is twice $K_\nu$ and with $\nu$ replaced by $-\nu$; its point is that the variable of integration is decoupled from $x$, which enters only through $x^2/(4\tau)$. It is used in the computation of the Mellin transform of a product of two Bessel kernels, [`LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq`](thm.html#LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq), in the archimedean analysis accompanying the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div.lean

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    besselKernel ν x =
      (((2 / x : ℝ)) : ℂ) ^ ν *
        ∫ τ in Set.Ioi (0 : ℝ), (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * ((τ : ℂ) ^ (ν - 1)) := by sorry
