-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_readable
-- name    : FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.120426+00:00
-- url     : https://prove2.me/theorems/95ce23ed-65af-442a-8f05-c357dc1dfec1
-- title:
--   Support Point On The Positive Side Of An Interior Point
-- statement:
--   This formalizes the support-side geometric ingredient associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a real inner-product normed additive group, let $\mu$ be a probability measure on $E$, and let $x_0\in E$ lie in the interior of the convex hull of the support of $\mu$. For every nonzero direction $u\in E$, there exists a support point $y$ such that
--   $$y\in\operatorname{supp}(\mu)\quad\text{and}\quad 0<\langle u,y-x_0\rangle.$$
--
--   This is a basic separation fact used to obtain positive-mass halfspace information around an interior point.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (μ : ProbabilityMeasure E) {x₀ : E}
--       (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
--       ∃ y ∈ (μ : Measure E).support, 0 < ⟪u, y - x₀⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Next: [`exists_pos_ball_inner_sub_pos_of_mem_support`](https://prove2.me/theorems/f71df184-ee7e-48db-81fc-c3549dfdd128).
--
--   [Source excerpt, lines 55–57](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L55-L57) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L53-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_readable (μ : ProbabilityMeasure E) {x₀ : E}
    (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
    ∃ y ∈ (μ : Measure E).support, 0 < ⟪u, y - x₀⟫ := by sorry
