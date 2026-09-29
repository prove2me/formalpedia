-- Prove2me | Theorems.Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
-- name    : LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/78cac85d-f151-56b7-93d6-f78d7f33f6bd
-- title:
--   Landau's lemma in logarithmic form
-- statement:
--   Let $d : \mathbb{N} \to \mathbb{R}$ satisfy $0 \le d(n)$ for every $n$, let $\Lambda : \mathbb{C} \to \mathbb{C}$ be a function, and let $x, \sigma_0$ be real numbers. Write $D$ for the $L$-series of the complex-valued coefficient function $n \mapsto (d(n) : \mathbb{C})$, so $D(s) = \sum_n d(n) n^{-s}$, summability meaning summability of the termwise family (equivalently, absolute convergence). Assume: (i) $\Lambda$ is analytic at every real point $\sigma$ with $x < \sigma$, viewed as a point of $\mathbb{C}$; and (ii) for every $s \in \mathbb{C}$ with $\sigma_0 < \operatorname{re} s$, the series defining $D(s)$ is summable and $\exp(D(s)) = \Lambda(s)$. No inequality between $x$ and $\sigma_0$ is assumed. The conclusion is twofold: the abscissa of absolute convergence of $n \mapsto (d(n) : \mathbb{C})$, as an element of $\overline{\mathbb{R}}$, is at most $x$; and for every real $\sigma > x$ the series defining $D(\sigma)$ is summable at the point $(\sigma : \mathbb{C})$ and satisfies $\exp(D(\sigma)) = \Lambda(\sigma)$.
--
--   This is a form of Landau's lemma for Dirichlet series with non-negative coefficients — convergence persists up to the first real singularity of the sum — adapted to the situation in which the analytic continuation is given for the exponential $\exp D$ rather than for $D$ itself, and only along the real ray. It is used in the analytic input to the study of arithmetic automorphic forms, in particular in the bounds on Euler-product twists and on weighted sums of squared Fourier coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.lean

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
    (d : ℕ → ℝ) (hd : ∀ n : ℕ, 0 ≤ d n) (Λ : ℂ → ℂ) (x σ₀ : ℝ)
    (han : ∀ σ : ℝ, x < σ → AnalyticAt ℂ Λ (σ : ℂ))
    (heq : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s) :
    LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ (x : EReal) ∧
      ∀ σ : ℝ, x < σ →
        LSeriesSummable (fun n => (d n : ℂ)) σ ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) σ) = Λ σ := by sorry
