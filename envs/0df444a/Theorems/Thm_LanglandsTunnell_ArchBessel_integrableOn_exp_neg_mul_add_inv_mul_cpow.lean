-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow
-- name    : LanglandsTunnell.ArchBessel.integrableOn_exp_neg_mul_add_inv_mul_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/bb5de16d-f43b-51d9-8004-5471bc244923
-- title:
--   Integrability of the K-Bessel integrand on (0,∞)
-- statement:
--   Let $\nu$ be a complex number and let $x$ be a real number with $0 < x$. The assertion is that the function $$t \mapsto e^{-x(t + t^{-1})/2}\, t^{\nu-1},$$ where the real exponential factor is regarded as a complex number and $t^{\nu-1}$ denotes the complex power of the real number $t$ coerced into $\mathbb{C}$, is integrable on the open half-line $(0,\infty)$, that is, integrable with respect to the restriction of Lebesgue measure to $\mathrm{Ioi}\,0$. No restriction whatsoever is placed on $\nu$: the statement holds for every complex exponent, the positivity of $x$ alone being what forces absolute convergence at both endpoints.
--
--   This is the absolute convergence of the classical integral representation of the Macdonald $K$-Bessel function, $e^{-x(t+t^{-1})/2}t^{\nu-1}$ being the integrand of the kernel $k_\nu(x)$. It is the convergence input used by [`LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel`](thm.html#LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel) and by [`LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub`](thm.html#LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub), i.e. for the differentiation of the kernel in $x$ and for its recurrence in the index $\nu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow.lean

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.integrableOn_exp_neg_mul_add_inv_mul_cpow (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by sorry
