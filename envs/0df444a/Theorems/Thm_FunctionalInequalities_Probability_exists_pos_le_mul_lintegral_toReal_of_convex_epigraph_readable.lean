-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable
-- name    : FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.011936+00:00
-- url     : https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000
-- title:
--   Pointwise Convex Potential Bound By Its Integral
-- statement:
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure and let $x_0$ belong to the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $C\in\mathbb R$ with $C>0$ such that, for every $\phi:E\to\overline{\mathbb R}$ satisfying:
--
--   1. $\phi(x)\ge0$ for every $x$.
--   2. Its real epigraph is convex.
--   3. $x\mapsto\phi(x).\operatorname{toENNReal}$ is a.e. measurable with respect to $\mu$.
--   4. Its lower integral is finite:
--      $$\int^- \phi(x).\operatorname{toENNReal}\,d\mu\ne+\infty.$$
--
--   one has
--   $$\phi(x_0)\le\left(C\left(\int^- \phi(x).\operatorname{toENNReal}\,d\mu\right).\operatorname{toReal}:\mathbb R\right).$$
--
--   The constant is selected from $\mu$ and $x_0$ before the potential $\phi$; this is the principal point-control estimate reused in the coercivity arguments.
--
--   **Formalization Note** The integral is an `ENNReal` lower integral, and `.toReal` converts it to $\mathbb R$ before the product is coerced back to the extended reals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_le_mul_lintegral_toReal_of_convex_epigraph [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
--       (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
--       x₀ ∈ interior (convexHull ℝ μ.support) →
--         ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
--           (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
--           AEMeasurable (fun x => (φ x).toENNReal) μ →
--           (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
--             φ x₀ ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂μ).toReal : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Supporting theorems: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`](https://prove2.me/theorems/2e3067a3-8fdf-4402-9d95-d8eb776cd1f3), [`mem_interior_setOf_ne_top_of_lintegral_ne_top`](https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d), [`strict_sublevel_convex_and_interior`](https://prove2.me/theorems/463b9839-1217-4882-805b-3a7aca81934e).
--
--   Previous: [`strict_sublevel_convex_and_interior`](https://prove2.me/theorems/463b9839-1217-4882-805b-3a7aca81934e) · Next: [`zero_mem_interior_convexHull_support_of_integral_eq_zero`](https://prove2.me/theorems/24d566b9-c33c-4ef2-a315-a7ad900693e2).
--
--   [Source excerpt, lines 654–661](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L654-L661) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Pointwise bound by the integral.”
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L651-L690 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_readable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
        (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          φ x₀ ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂μ).toReal : ℝ) : EReal) := by sorry
