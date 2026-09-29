-- Prove2me | Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
-- name    : MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d41dafd8-7dd1-5b6b-8423-cc4f7c1b10ca
-- title:
--   Smoothness of a parametric integral of a smooth compactly supported kernel
-- statement:
--   Let $X$ be a second-countable topological space equipped with a measurable structure for which open sets are measurable, and let $\mu$ be a measure on $X$ that is finite on compact sets. Let $M$, $P$ and $E$ be real normed additive commutative groups with real normed space structures, with $E$ complete. Given a continuous map $c \colon X \to M$, a continuous function $w \colon X \to \mathbb{R}$ whose support has compact closure, and a map $\Psi \colon M \times P \to E$ that is $C^\infty$ over $\mathbb{R}$ (smoothness index $\top$ in $\mathbb{N}_\infty$) and whose support has compact closure, the conclusion is that the function
--   $$p \longmapsto \int_X w(x)\,\Psi(c(x),p)\,d\mu(x)$$
--   from $P$ to $E$ is $C^\infty$ over $\mathbb{R}$. Note that $M$, $P$ and $E$ are required to live in the lowest universe, as the proof passes from $E$ to the space of continuous linear maps $P \to_L E$.
--
--   This is the standard statement that differentiation under the integral sign may be iterated indefinitely for a smooth compactly supported kernel integrated against a continuous compactly supported weight, in the form needed to see that partial integrals over a group or space $X$ depend smoothly on the remaining parameter $p$. It is used repeatedly in the archimedean part of the construction of automorphic forms, for instance in [`AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar`](thm.html#AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar) and in the production of smooth compactly supported test functions with prescribed integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {M P E : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (Ψ : M × P → E) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by sorry
