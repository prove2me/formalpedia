-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ConvexOn_ae_differentiableAt_of_isOpen_readable
-- name    : FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:33.804747+00:00
-- url     : https://prove2.me/theorems/b601dd62-f116-4daf-a684-024dc3b2b841
-- title:
--   Almost-Everywhere Differentiability of Convex Functions
-- statement:
--   This statement gives almost-everywhere differentiability of a convex function on an open set.
--
--   Let $E$ be a finite-dimensional real normed space with its Borel measurable structure, let $\mu$ be an additive Haar measure on $E$, and let $U\subseteq E$ be open. If $f:E\to\mathbb R$ is convex on $U$, then
--
--   $$
--   \text{for }\mu\text{-almost every }x,\quad x\in U\implies f\text{ is differentiable at }x.
--   $$
--
--   Equivalently, the exceptional set of points in $U$ where differentiability fails is $\mu$-null. This technical result supports almost-everywhere arguments involving subgradients of convex functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ConvexOn.ae_differentiableAt_of_isOpen {E : Type*} [NormedAddCommGroup E]
--       [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       (μ : Measure E) [μ.IsAddHaarMeasure]
--       {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
--       ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e) · Next: [`hasFDerivAt_of_convexOn_of_unique_subgradient`](https://prove2.me/theorems/690ed838-72ba-4da4-b243-c587f4147186).
--
--   [Source excerpt, lines 569–573](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L569-L573) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L567-L618 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open MeasureTheory Set

theorem FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_readable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by sorry
