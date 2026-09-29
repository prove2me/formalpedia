-- Prove2me | Theorems.Thm_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
-- name    : MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/de89162f-0741-59af-b188-743042dd9fa7
-- title:
--   Holomorphy and real positivity of dominated parameter integrals
-- statement:
--   Let $Y$ be a topological space with a measurable space structure whose open sets are measurable, let $\mu$ be a measure on $Y$, let $a \in \mathbb{R}$, and let $F : \mathbb{C} \to Y \to \mathbb{C}$. Assume: for each $s \in \mathbb{C}$ the function $F(s, \cdot)$ is almost everywhere strongly measurable for $\mu$; for each $y \in Y$ the function $s \mapsto F(s,y)$ is differentiable on all of $\mathbb{C}$; for every $s_0$ with $\operatorname{Re} s_0 > a$ there are $\varepsilon > 0$ and an integrable $M : Y \to \mathbb{R}$ with $\|F(s,y)\| \le M(y)$ for all $s$ in the ball of radius $\varepsilon$ about $s_0$ and all $y \in Y$; for every real $\sigma > a$ and every $y$, $F(\sigma, y)$ has vanishing imaginary part and non-negative real part; for every real $\sigma > a$ the function $F(\sigma, \cdot)$ is continuous; and there is a point $y_0 \in Y$ with $\operatorname{Re} F(\sigma, y_0) > 0$ for all real $\sigma > a$ and such that every open set containing $y_0$ has positive measure. Then $F(s, \cdot)$ is $\mu$-integrable whenever $\operatorname{Re} s > a$; the function $s \mapsto \int_Y F(s,y)\,d\mu(y)$ is analytic on a neighbourhood of each point of the half-plane $\{\operatorname{Re} s > a\}$; and for every real $\sigma > a$ the integral $\int_Y F(\sigma,y)\,d\mu(y)$ has imaginary part $0$ and strictly positive real part.
--
--   This is the analytic envelope for the $S$-parts of Rankin–Selberg type integrals: holomorphy in a half-plane of a parameter integral under local integrable domination, together with reality and strict positivity along the real points of that half-plane. It is used by [`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery), where the arithmetic input is the construction of the local majorant and of the point $y_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    (a : ℝ) (F : ℂ → Y → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ)
    (hhol : ∀ y : Y, Differentiable ℂ (fun s => F s y))
    (hdom : ∀ s₀ : ℂ, a < s₀.re → ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M μ ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ y : Y, ‖F s y‖ ≤ M y)
    (hreal : ∀ σ : ℝ, a < σ → ∀ y : Y, (F σ y).im = 0 ∧ 0 ≤ (F σ y).re)
    (hcont : ∀ σ : ℝ, a < σ → Continuous (F σ))
    (y₀ : Y) (hpt : ∀ σ : ℝ, a < σ → 0 < (F σ y₀).re)
    (hopen : ∀ U : Set Y, IsOpen U → y₀ ∈ U → 0 < μ U) :
    (∀ s : ℂ, a < s.re → Integrable (F s) μ) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ → (∫ y, F σ y ∂μ).im = 0 ∧ 0 < (∫ y, F σ y ∂μ).re) := by sorry
