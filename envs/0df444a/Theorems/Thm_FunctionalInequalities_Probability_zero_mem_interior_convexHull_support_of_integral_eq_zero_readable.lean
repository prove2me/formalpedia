-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_zero_mem_interior_convexHull_support_of_integral_eq_zero_readable
-- name    : FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:47.644536+00:00
-- url     : https://prove2.me/theorems/24d566b9-c33c-4ef2-a315-a7ad900693e2
-- title:
--   Interior Support Convex Hull from Centering and Nondegeneracy
-- statement:
--   This proves that the origin is an interior support point under centering and full-dimensionality assumptions.
--
--   Let $\mu$ be a nonzero finite Borel measure on a finite-dimensional real inner-product space. Assume:
--
--   1. no proper linear subspace carries all of $\mu$;
--   2. the identity map is integrable;
--   3. the barycenter is zero:
--      $$
--      \int x\,d\mu(x)=0.
--      $$
--
--   Then
--
--   $$
--   0\in\operatorname{int}\bigl(\operatorname{conv}(\operatorname{supp}\mu)\bigr).
--   $$
--
--   This geometric statement supplies the origin-interior hypothesis used in normalization and convex-support arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem zero_mem_interior_convexHull_support_of_integral_eq_zero {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
--       (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
--       (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
--       (0 : E) ∈ interior (convexHull ℝ μ.support)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Previous: [`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`](https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000).
--
--   [Source excerpt, lines 709–714](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L709-L714) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L707-L774 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory

theorem FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    (0 : E) ∈ interior (convexHull ℝ μ.support) := by sorry
