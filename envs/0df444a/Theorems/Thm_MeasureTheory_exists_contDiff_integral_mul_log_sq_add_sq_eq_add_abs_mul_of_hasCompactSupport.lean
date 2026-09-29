-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
-- name    : MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/bc008d8b-55d7-5ced-bd9a-30909dc53bcc
-- title:
--   Logarithmic potential integral splits as A+|ρ|B
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $g : E \times \mathbb{R} \to \mathbb{C}$ be infinitely differentiable (of class $C^\infty$ over $\mathbb{R}$) with compact support. The assertion is that there exist functions $A, B : E \times \mathbb{R} \to \mathbb{C}$, both of class $C^\infty$ on all of $E \times \mathbb{R}$, such that for every $e \in E$ and every $\rho \in \mathbb{R}$ the Bochner integral of $s \mapsto g(e,s)\,\log(s^2+\rho^2)$ over $\mathbb{R}$ (with respect to Lebesgue measure, the real logarithm being viewed in $\mathbb{C}$) satisfies $$\int_{\mathbb{R}} g(e,s)\,\log(s^2+\rho^2)\,ds \;=\; A(e,\rho) + |\rho|\,B(e,\rho).$$ Thus the parametric logarithmic potential, which is smooth away from $\rho = 0$ but only continuous there, is decomposed globally into a smooth part and $|\rho|$ times a smooth part, uniformly in the auxiliary parameter $e$. Note that the conclusion is the two-sided form in $\rho$ on the whole line, not a statement about $\rho \ge 0$ or about functions of $\rho^2$; no normalisation or support condition is imposed on $A$ and $B$.
--
--   This is the standard description of the singularity of the one-dimensional logarithmic kernel $\log(s^2+\rho^2)$ smeared against a smooth compactly supported density, in a form with smooth dependence on extra parameters. It is the analytic input for the archimedean computations at a real place, where it is applied to iterated integrals of the same shape and to integrals of $\log$ of a norm expression.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ A B : E × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (e : E) (ρ : ℝ),
        ∫ s : ℝ, g (e, s) * (Real.log (s ^ 2 + ρ ^ 2) : ℂ) = A (e, ρ) + ((|ρ| : ℝ) : ℂ) * B (e, ρ) := by sorry
