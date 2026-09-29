-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq
-- name    : LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a71d7459-7265-5945-a7d7-7a9a7727958a
-- title:
--   Mellin transform of a product of two Bessel kernels
-- statement:
--   Fix complex numbers $\mu$, $\nu$, $s$, and write $k_\lambda$ for the kernel $k_\lambda(x) = \int_0^\infty e^{-x(t+t^{-1})/2}\, t^{\lambda-1}\,dt$ (the Lebesgue integral over $(0,\infty)$ defining `besselKernel`, with the exponential coerced to $\mathbb{C}$). Under the single hypothesis $|\operatorname{Re}\mu| + |\operatorname{Re}\nu| < \operatorname{Re} s$, two assertions are made about the function $x \mapsto k_\mu(x)\,k_\nu(x)$ on $\mathbb{R}$. First, its Mellin transform converges at $s$ in the sense of Mathlib's `MellinConvergent`, i.e. $x \mapsto x^{s-1}\,k_\mu(x)\,k_\nu(x)$ is integrable for Lebesgue measure restricted to $(0,\infty)$. Second, the value of that Mellin transform is
--   $$\int_0^\infty k_\mu(x)\,k_\nu(x)\,x^{s-1}\,dx \;=\; 2^{\,s-1}\,\frac{\Gamma\!\left(\tfrac{s+\mu+\nu}{2}\right)\Gamma\!\left(\tfrac{s+\mu-\nu}{2}\right)\Gamma\!\left(\tfrac{s-\mu+\nu}{2}\right)\Gamma\!\left(\tfrac{s-\mu-\nu}{2}\right)}{\Gamma(s)},$$
--   with $\Gamma$ the complex Gamma function and $2^{s-1}$ the complex power.
--
--   This is the classical Bessel-kernel integral of Watson's treatise (§13.45): since $k_\nu(x) = 2K_\nu(x)$ for $x>0$, it is the evaluation $\int_0^\infty K_\mu K_\nu\,x^{s-1}\,dx = 2^{s-3}\prod \Gamma\!\left(\tfrac{s\pm\mu\pm\nu}{2}\right)/\Gamma(s)$, i.e. the archimedean Rankin–Selberg local integral for a pair of principal series of $\mathrm{GL}_2(\mathbb{R})$. It is used in the Rankin–Selberg package over $\mathbb{Q}$, where it supplies the Gamma-factor identity behind the entirety and normalisation statement [`LanglandsTunnell.RankinSelberg.exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one`](thm.html#LanglandsTunnell.RankinSelberg.exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq.lean

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq (μ ν s : ℂ) (hs : |μ.re| + |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel μ x * besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel μ x * besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma ((s + μ - ν) / 2) *
            Complex.Gamma ((s - μ + ν) / 2) * Complex.Gamma ((s - μ - ν) / 2)) / Complex.Gamma s := by sorry
