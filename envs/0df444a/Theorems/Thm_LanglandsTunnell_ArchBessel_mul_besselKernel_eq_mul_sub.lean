-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub
-- name    : LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/d2c3d82a-3419-5248-b285-42f2100d918d
-- title:
--   Index recurrence for the Bessel kernel
-- statement:
--   For a complex parameter $\nu$ and a real number $x$ with $0 < x$, write $k_\nu(x)$ for the quantity `besselKernel ν x`, defined as the Bochner integral over the open half-line $(0,\infty)$ of the function $t \mapsto e^{-(x(t+t^{-1})/2)} \, t^{\nu-1}$, where the real exponential factor is regarded as a complex number and $t^{\nu-1}$ is the complex power of the real variable $t$. The assertion is the identity $$\nu \, k_\nu(x) = \frac{x}{2}\bigl(k_{\nu+1}(x) - k_{\nu-1}(x)\bigr)$$ in $\mathbb{C}$, with $x$ coerced to a complex number on the right-hand side and the two kernels taken at the shifted parameters $\nu+1$ and $\nu-1$ at the same point $x$. No restriction is placed on $\nu$: positivity of $x$ alone guarantees, via `integrableOn_exp_neg_mul_add_inv_mul_cpow`, that all three integrals converge absolutely on $(0,\infty)$, so each of the three values appearing is the honest integral rather than a conditional limit.
--
--   This is the classical contiguous (index) relation $K_{\nu-1}(x) - K_{\nu+1}(x) = -(2\nu/x) K_\nu(x)$ for the modified Bessel function of the second kind, expressed for the integral kernel $k_\nu$ used here; it is obtained by integrating the derivative of $t^{\nu} e^{-x(t+t^{-1})/2}$ over $(0,\infty)$, the boundary contributions vanishing at both ends. It is used in establishing differentiability of $x \mapsto k_\nu(x)$ together with the corresponding statement for its derivative, which in turn feeds the analysis of the archimedean components of principal-series Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.lean

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) := by sorry
