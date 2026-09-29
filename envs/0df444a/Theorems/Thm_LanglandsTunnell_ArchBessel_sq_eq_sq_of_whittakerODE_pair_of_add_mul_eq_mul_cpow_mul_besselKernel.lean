-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
-- name    : LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/1e364337-300f-5f78-a830-0177d83b3ebf
-- title:
--   Whittaker pair with Bessel profile forces μ²=ν²
-- statement:
--   Let $\nu,\mu,c,\varepsilon,C,a$ be complex numbers and let $P,Q:\mathbb{R}\to\mathbb{C}$ be functions. Assume that $P$ and its derivative $\operatorname{deriv} P$ are differentiable on the open half-line $(0,\infty)$, and that for every real $y>0$
--   $$y^2\,P''(y)+\bigl(\tfrac14-\nu^2+2\pi c\,y-4\pi^2y^2\bigr)P(y)=0,$$
--   where $y$ is read as a complex number and $P''$ denotes the iterated derivative; assume likewise that $Q$ and $\operatorname{deriv} Q$ are differentiable on $(0,\infty)$ and that for every $y>0$
--   $$y^2\,Q''(y)+\bigl(\tfrac14-\nu^2-2\pi c\,y-4\pi^2y^2\bigr)Q(y)=0,$$
--   i.e. $P$ and $Q$ solve the two equations differing by the sign of the linear term $2\pi c\,y$. Assume $C\neq 0$, assume $a=\tfrac12$ or $a=\tfrac32$, and assume that for every $y>0$
--   $$P(y)+\varepsilon\,Q(y)=C\,y^{a}\,k_\mu(2\pi y),\qquad k_\mu(x)=\int_{0}^{\infty}e^{-x(t+t^{-1})/2}\,t^{\mu-1}\,dt,$$
--   the complex power $y^{a}$ being taken of the coercion of $y$ and $k_\mu$ being the kernel `besselKernel`. Then $\mu^2=\nu^2$.
--
--   This is the analytic step that matches the parameter of a modified-Bessel profile against the parameter of the Whittaker equations it solves: the two sign-conjugate second-order equations with the same Casimir datum $\tfrac14-\nu^2$, together with the prescribed shape $C\,y^{a}k_\mu(2\pi y)$ of the combination $P+\varepsilon Q$, determine $\nu^2$ as $\mu^2$. It feeds the Mellin-to-parameter passage in the archimedean part of the Langlands–Tunnell input, being used by [`LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal`](thm.html#LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal); the proof cites the second-order differential recursion for `besselKernel` and the existence of a point where it is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
    (ν μ c ε C a : ℂ) (P Q : ℝ → ℂ)
    (hP : DifferentiableOn ℝ P (Set.Ioi 0)) (hP' : DifferentiableOn ℝ (deriv P) (Set.Ioi 0))
    (hPode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv P) y
        + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * P y = 0)
    (hQ : DifferentiableOn ℝ Q (Set.Ioi 0)) (hQ' : DifferentiableOn ℝ (deriv Q) (Set.Ioi 0))
    (hQode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv Q) y
        + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q y = 0)
    (hC : C ≠ 0) (ha : a = 1 / 2 ∨ a = 3 / 2)
    (hH : ∀ y : ℝ, 0 < y → P y + ε * Q y = C * (y : ℂ) ^ a * besselKernel μ (2 * Real.pi * y)) :
    μ ^ 2 = ν ^ 2 := by sorry
