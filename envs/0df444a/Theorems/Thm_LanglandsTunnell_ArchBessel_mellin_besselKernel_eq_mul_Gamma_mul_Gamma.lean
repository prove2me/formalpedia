-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma
-- name    : LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e81f5184-cc59-5bb4-b460-e70105a7c929
-- title:
--   Mellin transform of the Bessel kernel k_ν
-- statement:
--   Let $\nu, s \in \mathbb{C}$ satisfy $|\operatorname{Re}\nu| < \operatorname{Re} s$. The kernel in question is $\mathrm{besselKernel}\,\nu$, the function of a real variable $x$ given by the Bochner integral $$k_\nu(x) = \int_{t \in (0,\infty)} e^{-x(t+t^{-1})/2}\, t^{\nu-1}\,dt,$$ where the real exponential is coerced into $\mathbb{C}$ and $t^{\nu-1}$ is the complex power of the positive real $t$. The theorem asserts two things simultaneously. First, `MellinConvergent` holds for $x \mapsto k_\nu(x)$ at $s$, i.e. the function $x \mapsto x^{s-1} k_\nu(x)$ is integrable on $(0,\infty)$ with respect to the restriction of Lebesgue measure. Second, the value of the Mellin transform is $$\int_0^\infty k_\nu(x)\, x^{s-1}\,dx = 2^{\,s-1}\,\Gamma\!\left(\tfrac{s+\nu}{2}\right)\Gamma\!\left(\tfrac{s-\nu}{2}\right),$$ with $2^{s-1}$ the complex power and $\Gamma$ the complex Gamma function.
--
--   Since $k_\nu = 2K_\nu$ for the Macdonald function $K_\nu$, this is the classical formula $\int_0^\infty K_\nu(x)x^{s-1}\,dx = 2^{s-2}\Gamma((s+\nu)/2)\Gamma((s-\nu)/2)$, valid in the strip $\operatorname{Re} s > |\operatorname{Re}\nu|$. It underlies the archimedean computation in the principal-series branch of the Rankin–Selberg package, being used to characterise $k_\nu$ by its Mellin transform and to exhibit a point where $k_\nu$ is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma.lean

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by sorry
