-- Prove2me | Theorems.Thm_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace
-- name    : MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/267545d9-a0b7-5723-adb3-49aaa2a9b533
-- title:
--   Smoothness of the logarithmic potential on a closed half-space
-- statement:
--   Let $E$ be a finite-dimensional real normed space (a normed additive commutative group with a real normed space structure), and let $g : E \times \mathbb{R} \to \mathbb{C}$ be a function which is $C^\infty$ on all of $E \times \mathbb{R}$ (`ContDiff ℝ ⊤`) and has compact support. Consider the function of two arguments $p = (e, \rho) \in E \times \mathbb{R}$ given by the Bochner integral with respect to Lebesgue measure on $\mathbb{R}$,
--   $$F(e,\rho) \;=\; \int_{\mathbb{R}} g(e,s)\,\log\bigl(s^{2} + \rho^{2}\bigr)\,ds,$$
--   where $\log$ is the real logarithm (so, by Mathlib's convention, the integrand vanishes at the single point $s = \rho = 0$) and its value is coerced into $\mathbb{C}$. The assertion is that $F$ is $C^\infty$ on the closed half-space $\{p \in E \times \mathbb{R} : 0 \le p.2\}$ in the sense of `ContDiffOn ℝ ⊤`, i.e. for every finite order there are continuous derivatives within that set, one-sided in the $\rho$-direction at the boundary $\rho = 0$. No smoothness across $\rho = 0$ is claimed, and indeed none holds in general.
--
--   This is the classical regularity statement for a logarithmic potential with parameters: although $F$ is even in $\rho$ and typically behaves like $c(e) + 2\pi g(e,0)\,|\rho| + \dots$ near the boundary, it is smooth up to the boundary from each side. It feeds the decomposition result [`MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport`](thm.html#MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport), which splits such a potential into a globally smooth part plus $|\rho|$ times a smooth part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_contDiffOn_integral_mul_log_sq_add_sq_halfSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.contDiffOn_integral_mul_log_sq_add_sq_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E × ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × ℝ => ∫ s : ℝ, g (p.1, s) * (Real.log (s ^ 2 + p.2 ^ 2) : ℂ))
      {p : E × ℝ | 0 ≤ p.2} := by sorry
