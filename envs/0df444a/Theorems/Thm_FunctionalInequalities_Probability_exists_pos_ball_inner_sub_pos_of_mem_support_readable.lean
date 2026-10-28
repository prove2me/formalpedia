-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_ball_inner_sub_pos_of_mem_support_readable
-- name    : FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:50.685801+00:00
-- url     : https://prove2.me/theorems/f71df184-ee7e-48db-81fc-c3549dfdd128
-- title:
--   Positive-Mass Ball Stable Under Nearby Halfspace Directions
-- statement:
--   This is a local support and halfspace lemma used in the geometric argument for Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a real inner-product normed additive group, let $\mu$ be a probability measure, and let $x_0,u,y\in E$. Assume that $y\in\operatorname{supp}(\mu)$ and
--   $$0<\langle u,y-x_0\rangle.$$
--   Then there exist $\delta>0$ and $r>0$ such that the ball $B(y,r)$ has strictly positive $\mu$-measure and, for every $v\in E$ with $\|v-u\|<\delta$ and every $x\in B(y,r)$,
--   $$0<\langle v,x-x_0\rangle.$$
--
--   The result supplies a positive-mass neighborhood on which nearby directions define strict open halfspaces.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_ball_inner_sub_pos_of_mem_support (μ : ProbabilityMeasure E) {x₀ u y : E}
--       (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u, y - x₀⟫) :
--       ∃ δ > 0, ∃ r > 0, 0 < (μ : Measure E) (Metric.ball y r) ∧
--         ∀ v : E, ‖v - u‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Previous: [`exists_mem_support_inner_sub_pos_of_mem_interior_convexHull`](https://prove2.me/theorems/95ce23ed-65af-442a-8f05-c357dc1dfec1) · Next: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`](https://prove2.me/theorems/b1dc5e60-c703-4418-988d-32b752eb87e5).
--
--   [Source excerpt, lines 112–115](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L112-L115) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L110-L219 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_readable (μ : ProbabilityMeasure E) {x₀ u y : E}
    (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u, y - x₀⟫) :
    ∃ δ > 0, ∃ r > 0, 0 < (μ : Measure E) (Metric.ball y r) ∧
      ∀ v : E, ‖v - u‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by sorry
