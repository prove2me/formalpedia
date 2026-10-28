-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_mem_interior_setOf_ne_top_of_lintegral_ne_top_readable
-- name    : FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.339027+00:00
-- url     : https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d
-- title:
--   Interior of the Effective Domain from Finite Integral
-- statement:
--   This is the effective-domain interior lemma corresponding to Lemma 16 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $E$ be finite-dimensional, let $\mu$ be a finite Borel measure, and let $x_0$ lie in the interior of the convex hull of $\operatorname{supp}\mu$. Let $\phi:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi\geq0$;
--   2. its real epigraph is convex;
--   3. $x\mapsto\phi(x).\operatorname{toENNReal}$ is almost everywhere measurable;
--   4. $\int^\infty \phi.\operatorname{toENNReal}\,d\mu\neq+\infty$.
--
--   Then
--
--   $$
--   x_0\in\operatorname{int}\{x:\phi(x)\neq+\infty\}.
--   $$
--
--   Thus finite extended-real integral control forces finiteness on a neighborhood of every interior support point.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mem_interior_setOf_ne_top_of_lintegral_ne_top [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
--       x₀ ∈ interior (convexHull ℝ μ.support) →
--         ∀ φ : E → EReal, (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
--           AEMeasurable (fun x => (φ x).toENNReal) μ →
--           (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
--             x₀ ∈ interior {x | φ x ≠ ⊤}
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Previous: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`](https://prove2.me/theorems/b1dc5e60-c703-4418-988d-32b752eb87e5) · Next: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`](https://prove2.me/theorems/2e3067a3-8fdf-4402-9d95-d8eb776cd1f3).
--
--   [Source excerpt, lines 434–439](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L434-L439) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L432-L463 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

theorem FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_readable [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∀ φ : E → EReal, (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          x₀ ∈ interior {x | φ x ≠ ⊤} := by sorry
