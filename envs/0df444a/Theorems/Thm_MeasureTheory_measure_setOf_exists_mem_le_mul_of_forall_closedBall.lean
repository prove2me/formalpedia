-- Prove2me | Theorems.Thm_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall
-- name    : MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2e52ed06-8952-59a7-b52d-15dcf64d1feb
-- title:
--   Besicovitch propagation of a hitting bound from small balls
-- statement:
--   Let $\alpha$ be a metric space which is second countable, carries a measurable space structure for which the open sets are measurable, and satisfies Mathlib's Besicovitch covering property (`HasBesicovitchCovering`), and let $\beta$ be a measurable space. Let $\mu$ be a measure on $\beta$ and $\nu$ an $s$-finite, outer regular measure on $\alpha$. Let $P : \beta \to \alpha \to \mathrm{Prop}$ be an arbitrary relation, $S \subseteq \alpha$ an arbitrary subset, and $K \in [0,\infty]$ with $K \neq \infty$. Assume that for every $x \in S$ there exists $\delta > 0$ such that for every radius $\rho$ with $0 < \rho < \delta$,
--   $$\mu\{b : \exists\, y \in \overline{B}(x,\rho),\ P\,b\,y\} \le K \cdot \nu\bigl(\overline{B}(x,\rho)\bigr).$$
--   Then
--   $$\mu\{b : \exists\, x \in S,\ P\,b\,x\} \le K \cdot \nu(S).$$
--   No measurability is assumed of the sets $\{b : \exists x \in S,\ P\,b\,x\}$, of the sets occurring in the hypothesis, or of $S$; the inequalities are inequalities of outer measures in $[0,\infty]$.
--
--   A propagation principle transferring a local estimate on small closed balls — the $\mu$-measure of the parameters $b$ hitting some point of $\overline{B}(x,\rho)$ is at most $K\,\nu(\overline{B}(x,\rho))$ — to the same estimate, with the same constant, for an arbitrary set $S$ of centres. It is used in the form [`Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume`](thm.html#Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume), where $\alpha = \mathbb{C}$ and $\nu$ is Lebesgue measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
    {α β : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [HasBesicovitchCovering α] {_ : MeasurableSpace β} (μ : Measure β) (ν : Measure α) [SFinite ν]
    [ν.OuterRegular] (P : β → α → Prop) (S : Set α) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ x ∈ S, ∃ δ > 0, ∀ ρ ∈ Set.Ioo 0 δ,
      μ {b | ∃ y ∈ Metric.closedBall x ρ, P b y} ≤ K * ν (Metric.closedBall x ρ)) :
    μ {b | ∃ x ∈ S, P b x} ≤ K * ν S := by sorry
