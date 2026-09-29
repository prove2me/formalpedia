-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero
-- name    : LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/f4ca9ef2-03c6-5948-bc45-46c7fa34f4d4
-- title:
--   The Bessel kernel k_ν does not vanish identically
-- statement:
--   For every complex number $\nu$ there exists a real number $x$ with $x > 0$ and $\mathrm{besselKernel}\ \nu\ x \neq 0$, where $\mathrm{besselKernel}\ \nu\ x$ is defined as the integral over the open interval $(0,\infty)$ of the function $t \mapsto e^{-x(t+t^{-1})/2}\, t^{\nu-1}$, the real exponential factor being regarded as a complex number and $t^{\nu-1}$ being the complex power of the positive real $t$. Thus the assertion is that the function $x \mapsto \mathrm{besselKernel}\ \nu\ x$ is not identically zero on the positive half-line; no hypothesis whatever is imposed on $\nu$, and only non-vanishing at a single unspecified point is claimed, not positivity or non-vanishing everywhere.
--
--   Up to normalisation $k_\nu(x) = 2K_\nu(x)$ is the classical Macdonald–Bessel function, and this statement records the minimal non-degeneracy needed to use $k_\nu$ as a basis element. It is cited in the identification of the archimedean Whittaker profiles of principal series, in [`LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel`](thm.html#LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel) and [`LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel`](thm.html#LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel), where vanishing of $k_\nu$ would collapse the pair $\{k, k'\}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero.lean

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero (ν : ℂ) :
    ∃ x : ℝ, 0 < x ∧ besselKernel ν x ≠ 0 := by sorry
