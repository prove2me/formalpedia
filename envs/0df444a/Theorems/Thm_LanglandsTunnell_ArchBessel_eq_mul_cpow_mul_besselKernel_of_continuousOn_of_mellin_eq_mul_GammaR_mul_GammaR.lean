-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR
-- name    : LanglandsTunnell.ArchBessel.eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/02f863cc-761d-5ded-b2ec-a4f26c0e3831
-- title:
--   Mellin uniqueness for a product of two Γ_ℝ-factors
-- statement:
--   Let $f:\mathbb R\to\mathbb C$ be a function, $A,p,q\in\mathbb C$ and $\sigma_0\in\mathbb R$. Assume $f$ is continuous on the open half-line $(0,\infty)$, and assume that for every $s\in\mathbb C$ with $\operatorname{Re}(s)>\sigma_0$ the Mellin integral $\int_0^\infty f(t)\,t^{s-1}\,dt$ converges (in Mathlib's sense, `MellinConvergent`) and its value is $$\operatorname{mellin} f(s)=A\,\Gamma_{\mathbb R}(s+p)\,\Gamma_{\mathbb R}(s+q),\qquad \Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2).$$ The conclusion is that $f$ is then pinned down pointwise on $(0,\infty)$: for every real $t>0$, $$f(t)=2A\,t^{(p+q)/2}\,k_{(p-q)/2}(2\pi t),$$ where $t^{(p+q)/2}$ is the complex power of the coercion of $t$ and $k_\nu$ is the kernel `besselKernel`, defined for $\nu\in\mathbb C$ and $x\in\mathbb R$ by the integral over $u\in(0,\infty)$ of $\exp\bigl(-x(u+u^{-1})/2\bigr)\,u^{\nu-1}$ (a Bessel $K$-integral up to normalisation). No positivity or growth condition beyond the stated convergence hypothesis is imposed, and $\sigma_0$ is arbitrary.
--
--   This is the Mellin-uniqueness step in the principal-series shape: a function on $(0,\infty)$ whose Mellin transform is a constant multiple of $\Gamma_{\mathbb R}(s+p)\Gamma_{\mathbb R}(s+q)$ on a right half-plane must be the corresponding Whittaker/Bessel profile, the comparison being made against the evaluation $\operatorname{mellin}(k_\nu)(s)=2^{s-1}\Gamma\bigl(\frac{s+\nu}{2}\bigr)\Gamma\bigl(\frac{s-\nu}{2}\bigr)$ recorded in [`LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma`](thm.html#LanglandsTunnell.ArchBessel.mellin_besselKernel_eq_mul_Gamma_mul_Gamma). It is used in the archimedean part of the Rankin–Selberg package over $\mathbb Q$ and in the identification of the Laplace eigenvalue attached to a principal-series archimedean parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR.lean

import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR
    (f : ℝ → ℂ) (A p q : ℂ) (σ₀ : ℝ)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hM : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = A * Complex.Gammaℝ (s + p) * Complex.Gammaℝ (s + q)) :
    ∀ t : ℝ, 0 < t →
      f t = 2 * A * ((t : ℂ) ^ ((p + q) / 2)) * besselKernel ((p - q) / 2) (2 * Real.pi * t) := by sorry
