-- Prove2me | Theorems.Thm_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top
-- name    : MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/0f087b95-fdd2-5124-9df6-869a13cffb10
-- title:
--   Finite unions of right translates have finite measure
-- statement:
--   Let $G$ be a group equipped with a measurable space structure for which multiplication is measurable, and let $\mu$ be a measure on $G$ that is invariant under right translation. Let $s \subseteq G$ be a set whose measure $\mu s$ is strictly less than $\infty$, and let $T$ be a finite subset of $G$. The conclusion is that the measure of the union $\bigcup_{x \in T} \{g x : g \in s\}$, that is, of the union over the elements $x$ of $T$ of the images of $s$ under right multiplication by $x$, is again strictly less than $\infty$. No measurability hypothesis on $s$ is required, the measure being taken in the sense of an outer measure on arbitrary sets; likewise no $\sigma$-finiteness or Haar-type hypothesis on $\mu$ beyond right invariance is assumed.
--
--   This is the elementary volume estimate saying that a window formed as a finite union of right translates of a set of finite measure still has finite measure. It is used in the analytic input to [`AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self`](thm.html#AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_self), where finiteness of the measure of such a window is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by sorry
