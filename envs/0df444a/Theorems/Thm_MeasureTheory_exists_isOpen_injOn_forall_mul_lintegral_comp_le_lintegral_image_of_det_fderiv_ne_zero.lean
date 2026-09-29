-- Prove2me | Theorems.Thm_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
-- name    : MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/17a9edcb-1f5a-59a9-9841-229b2a40ae0d
-- title:
--   Local lower bound for change of variables at a nondegenerate point
-- statement:
--   Let $E$ be a real normed additive commutative group carrying a normed $\mathbb{R}$-vector space structure, finite-dimensional over $\mathbb{R}$, with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be a measure on $E$ that is an additive Haar measure. Let $f\colon E\to E$ be a map and $a\in E$ a point such that $f$ is continuously differentiable of order $1$ at $a$ (in the sense of `ContDiffAt ℝ 1 f a`) and such that the determinant of the Fréchet derivative $\operatorname{fderiv}_{\mathbb{R}} f\,a$ is nonzero. Then there is a set $s\subseteq E$ which is open and contains $a$, on which $f$ is injective, and there is a nonnegative real $\delta>0$ such that for every measurable set $t\subseteq s$ and every function $g\colon E\to[0,\infty]$ (no measurability of $g$ assumed, the integrals being lower Lebesgue integrals with respect to $\mu$),
--   $$\delta\int_t^{-} g(f(x))\,d\mu(x)\ \le\ \int_{f(t)}^{-} g(y)\,d\mu(y).$$
--
--   This is the local change-of-variables formula at a point where the derivative is invertible, in the one-sided form of an inequality with a uniform constant, valid for arbitrary nonnegative functions. It is used in the archimedean analytic part of the development, where it supports [`AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le`](thm.html#AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

theorem MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (a : E) (hf : ContDiffAt ℝ 1 f a) (hf' : (fderiv ℝ f a).det ≠ 0) :
    ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ Set.InjOn f s ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t ⊆ s, MeasurableSet t → ∀ g : E → ℝ≥0∞,
        (δ : ℝ≥0∞) * ∫⁻ x in t, g (f x) ∂μ ≤ ∫⁻ y in f '' t, g y ∂μ := by sorry
