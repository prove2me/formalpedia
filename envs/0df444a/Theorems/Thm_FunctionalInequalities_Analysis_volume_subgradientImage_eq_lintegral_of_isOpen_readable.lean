-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_eq_lintegral_of_isOpen_readable
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:54.562295+00:00
-- url     : https://prove2.me/theorems/a875c8d6-d13c-4184-b1ba-d8541c085171
-- title:
--   Open-Set Alexandrov Volume Formula
-- statement:
--   This is the Alexandrov volume identity for open sets in the moment-map setting.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume
--   $$\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1.$$
--   Let $K\subseteq E$ be closed and convex, let $V:E\to\mathbb R$ be measurable, and suppose the push-forward of the tilted volume measure by $\nabla u$ equals the measure with density
--   $$1_K(p)\,\operatorname{ofReal}(e^{-V(p)}).$$
--   Then every open set $G\subseteq E$ satisfies
--   $$\operatorname{vol}(\partial u(G))
--   =\int_G \operatorname{ofReal}\!\left(e^{-u(x)+V(\nabla u(x))}\right)\,d\operatorname{vol}(x).$$
--
--   This formula is a central measure identity for the moment potential and is used to derive local Monge–Ampère bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem volume_subgradientImage_eq_lintegral_of_isOpen [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
--       {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
--       (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
--         (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
--       {G : Set E} (hG : IsOpen G) :
--       (volume : Measure E) (subgradientImage u G) =
--         ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`lintegral_subgradientImage_eq_of_map_gradient`](https://prove2.me/theorems/72af9bcf-0597-4b8f-9f71-0ba93a4e8609), [`subgradient_mem_of_ae_gradient_mem`](https://prove2.me/theorems/6f655218-b30e-46bf-be4f-c590531dd524).
--
--   Previous: [`subgradientImage_sub_inner_add_const`](https://prove2.me/theorems/8b64958d-7cd7-4f0c-96e8-9c9b1e0139d2) · Next: [`exists_inverse_subgradient_volume_bounds`](https://prove2.me/theorems/d2723f7d-8cba-4654-bce4-6f99044af824).
--
--   [Source excerpt, lines 2194–2202](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2194-L2202) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2191-L2329 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {G : Set E} (hG : IsOpen G) :
    (volume : Measure E) (subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E) := by sorry
