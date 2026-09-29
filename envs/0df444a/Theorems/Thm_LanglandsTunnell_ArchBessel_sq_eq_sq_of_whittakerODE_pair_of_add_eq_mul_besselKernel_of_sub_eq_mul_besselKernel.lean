-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel
-- name    : LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/bdc88c38-b005-51ad-8118-de2ae96d569d
-- title:
--   Bessel profiles of mixed-sign Whittaker solutions force (μ+tfrac12)²=ν²
-- statement:
--   Write $k_\nu(x) = \int_0^\infty e^{-x(t+t^{-1})/2}\,t^{\nu-1}\,dt$ for the kernel `besselKernel`. Let $\nu,\mu,c,C_0,C_1$ be complex numbers and let $P,Q : \mathbb{R} \to \mathbb{C}$ be functions such that $P$ and its derivative $\operatorname{deriv} P$ are differentiable on $(0,\infty)$, and likewise $Q$ and $\operatorname{deriv} Q$. Assume that for every real $y>0$ the two Whittaker-type equations of opposite sign in $c$ hold, namely $y^2 P''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi c\,y - 4\pi^2 y^2\bigr) P(y) = 0$ and $y^2 Q''(y) + \bigl(\tfrac14 - \nu^2 - 2\pi c\,y - 4\pi^2 y^2\bigr) Q(y) = 0$, the second derivatives being the iterated derivative $\operatorname{deriv}(\operatorname{deriv} P)$ and $\operatorname{deriv}(\operatorname{deriv} Q)$ and the coefficients read in $\mathbb{C}$ with $y$ coerced from $\mathbb{R}$. Assume further that $C_0 \neq 0$, that $C_1 \neq 0$, and that for all $y>0$ one has $P(y) + Q(y) = C_0\,y\,k_\mu(2\pi y)$ and $P(y) - Q(y) = C_1\,y\,k_{\mu+1}(2\pi y)$. Then $(\mu + \tfrac12)^2 = \nu^2$.
--
--   This is the mixed-sign (weight-one type) half of the passage from a Bessel-type Mellin expansion to an identity between spectral parameters in the archimedean analysis underlying the Langlands–Tunnell theorem: the shape of the symmetrised solutions pins the Bessel index $\mu$ to the Whittaker parameter $\nu$. It is used by [`LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal`](thm.html#LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal), where $\mu$ is built from the two principal-series exponents, and it rests on the differential relations for `besselKernel` recorded in [`LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel`](thm.html#LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel) together with the non-vanishing statement [`LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero`](thm.html#LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_eq_mul_besselKernel_of_sub_eq_mul_besselKernel
    (ν μ c C₀ C₁ : ℂ) (P Q : ℝ → ℂ)
    (hP : DifferentiableOn ℝ P (Set.Ioi 0)) (hP' : DifferentiableOn ℝ (deriv P) (Set.Ioi 0))
    (hPode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv P) y
        + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * P y = 0)
    (hQ : DifferentiableOn ℝ Q (Set.Ioi 0)) (hQ' : DifferentiableOn ℝ (deriv Q) (Set.Ioi 0))
    (hQode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv Q) y
        + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q y = 0)
    (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0)
    (hadd : ∀ y : ℝ, 0 < y → P y + Q y = C₀ * (y : ℂ) * besselKernel μ (2 * Real.pi * y))
    (hsub : ∀ y : ℝ, 0 < y → P y - Q y = C₁ * (y : ℂ) * besselKernel (μ + 1) (2 * Real.pi * y)) :
    (μ + 1 / 2) ^ 2 = ν ^ 2 := by sorry
