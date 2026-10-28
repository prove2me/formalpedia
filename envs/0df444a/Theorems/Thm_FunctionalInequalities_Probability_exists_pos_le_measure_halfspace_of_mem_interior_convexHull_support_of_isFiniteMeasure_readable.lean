-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable
-- name    : FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.480981+00:00
-- url     : https://prove2.me/theorems/2e3067a3-8fdf-4402-9d95-d8eb776cd1f3
-- title:
--   Uniform Halfspace Mass For A Finite Measure
-- statement:
--   This formalizes the finite-measure version of the halfspace estimate associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure, and assume $x_0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $m\in\mathbb R$ such that
--   $$0<m\le \mu(E)$$
--   and, for every $u\in E$ with $\|u\|=1$,
--   $$m\le \mu_{\mathrm{real}}\{x:\langle u,x-x_0\rangle>0\}.$$
--
--   The conclusion is uniform over all unit directions and uses the real-valued measure conversion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure {E : Type*}
--       [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (μ : Measure E) [IsFiniteMeasure μ] {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ μ.support)) :
--       ∃ m : ℝ, 0 < m ∧ m ≤ μ.real Set.univ ∧ ∀ u : E, ‖u‖ = 1 → m ≤ μ.real {x | 0 < ⟪u, x - x₀⟫}
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Supporting theorems: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`](https://prove2.me/theorems/b1dc5e60-c703-4418-988d-32b752eb87e5).
--
--   Previous: [`mem_interior_setOf_ne_top_of_lintegral_ne_top`](https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d) · Next: [`real_convexOn_effective_domain`](https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc).
--
--   [Source excerpt, lines 477–480](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L477-L480) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L475-L516 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ μ.support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ μ.real Set.univ ∧ ∀ u : E, ‖u‖ = 1 → m ≤ μ.real {x | 0 < ⟪u, x - x₀⟫} := by sorry
