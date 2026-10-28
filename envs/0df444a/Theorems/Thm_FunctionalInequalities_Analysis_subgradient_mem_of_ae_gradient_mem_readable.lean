-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_of_ae_gradient_mem_readable
-- name    : FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:54.701841+00:00
-- url     : https://prove2.me/theorems/6f655218-b30e-46bf-be4f-c590531dd524
-- title:
--   Subgradients Lie In Closed Convex Gradient Range
-- statement:
--   This proves containment of every subgradient in a closed convex range of the almost-everywhere gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Let $K\subseteq E$ be closed and convex, and assume
--   $$\nabla u(x)\in K\quad\text{for almost every }x\text{ with respect to volume}.$$
--   If $x,p\in E$ satisfy
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y\in E,$$
--   then
--   $$p\in K.$$
--
--   This is a support-and-closure principle used to control subgradient images.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradient_mem_of_ae_gradient_mem [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
--       (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
--       {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`contDiff_one_of_convexOn_of_differentiable`](https://prove2.me/theorems/16eb9c9c-a99f-4109-be05-1626be515a47) · Next: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   [Source excerpt, lines 150–154](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L150-L154) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L145-L186 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K := by sorry
