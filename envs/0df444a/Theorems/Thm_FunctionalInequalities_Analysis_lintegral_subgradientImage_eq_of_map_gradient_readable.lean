-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lintegral_subgradientImage_eq_of_map_gradient_readable
-- name    : FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:54.933881+00:00
-- url     : https://prove2.me/theorems/72af9bcf-0597-4b8f-9f71-0ba93a4e8609
-- title:
--   Subgradient Image Integral Identity
-- statement:
--   This is the Alexandrov identity in push-forward form.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Let $\nu,\mu$ be measures such that:
--
--   1. $\nu\ll\operatorname{vol}$.
--   2. The push-forward of $\nu$ by `gradient` equals $\mu$:
--      $$\nu\mathbin{\#}\nabla u=\mu.$$
--   3. $\mu\ll\operatorname{vol}$.
--   4. $S\subseteq E$ is compact.
--   5. $g:E\to[0,\infty]$ is measurable.
--
--   Then, with `subgradientImage` denoting $\partial u(S)$,
--   $$\int_{\partial u(S)} g(p)\,d\mu(p)=\int_S g(\nabla u(x))\,d\nu(x).$$
--
--   The identity is a reusable change-of-variables formula; both sides are `ENNReal` lower integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_subgradientImage_eq_of_map_gradient [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       {ν μ : Measure E} (hν : ν ≪ (volume : Measure E)) (hmap : ν.map (gradient u) = μ)
--       (hac : μ ≪ (volume : Measure E))
--       {S : Set E} (hS : IsCompact S) (g : E → ℝ≥0∞) (hg : Measurable g) :
--       ∫⁻ p in subgradientImage u S, g p ∂μ = ∫⁻ x in S, g (gradient u x) ∂ν
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`volume_subgradient_two_points_eq_zero`](https://prove2.me/theorems/097fae72-0e02-4d52-bbb1-f4883ba49bd8).
--
--   Next: [`mem_subgradientImage_of_affine_le_of_nonneg_frontier`](https://prove2.me/theorems/f79e9028-f752-4900-ae74-36d3b8229978).
--
--   [Source excerpt, lines 78–83](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L78-L83) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L74-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {ν μ : Measure E} (hν : ν ≪ (volume : Measure E)) (hmap : ν.map (gradient u) = μ)
    (hac : μ ≪ (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in subgradientImage u S, g p ∂μ = ∫⁻ x in S, g (gradient u x) ∂ν := by sorry
