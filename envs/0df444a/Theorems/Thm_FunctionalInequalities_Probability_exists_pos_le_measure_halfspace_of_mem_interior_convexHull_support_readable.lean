-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable
-- name    : FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:43.938522+00:00
-- url     : https://prove2.me/theorems/b1dc5e60-c703-4418-988d-32b752eb87e5
-- title:
--   Uniform Positive Halfspace Mass For A Probability Measure
-- statement:
--   This formalizes the probability-measure halfspace estimate associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a finite-dimensional real inner-product normed additive group with a measurable Borel structure. Let $\mu$ be a probability measure and let $x_0$ lie in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $m\in\mathbb R$ such that
--   $$0<m\le 1$$
--   and, for every unit vector $u\in E$,
--   $$m\le \left(\mu\{x:\langle u,x-x_0\rangle>0\}\right).\operatorname{toReal}.$$
--
--   This gives a dimension-dependent uniform lower bound for all strict open halfspaces through $x_0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (μ : ProbabilityMeasure E) {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) :
--       ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
--         ∀ u : E, ‖u‖ = 1 → m ≤ ((μ : Measure E) {x | 0 < ⟪u, x - x₀⟫}).toReal
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Supporting theorems: [`exists_mem_support_inner_sub_pos_of_mem_interior_convexHull`](https://prove2.me/theorems/95ce23ed-65af-442a-8f05-c357dc1dfec1), [`exists_pos_ball_inner_sub_pos_of_mem_support`](https://prove2.me/theorems/f71df184-ee7e-48db-81fc-c3549dfdd128).
--
--   Previous: [`exists_pos_ball_inner_sub_pos_of_mem_support`](https://prove2.me/theorems/f71df184-ee7e-48db-81fc-c3549dfdd128) · Next: [`mem_interior_setOf_ne_top_of_lintegral_ne_top`](https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d).
--
--   [Source excerpt, lines 305–308](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L305-L308) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L304-L400 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E) {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ u : E, ‖u‖ = 1 → m ≤ ((μ : Measure E) {x | 0 < ⟪u, x - x₀⟫}).toReal := by sorry
