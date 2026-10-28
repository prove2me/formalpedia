-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_map_gradient_readable
-- name    : FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:15.073532+00:00
-- url     : https://prove2.me/theorems/0ffece2e-a383-4c75-b592-04da65ab3fa7
-- title:
--   Continuous Differentiability of the Moment Potential
-- statement:
--   This formalizes the regularity statement associated with Klartag's result, cited as Lemma 2.2 in Letwin (arXiv:2607.24164v1), with the reviewed relation recorded as partial.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume:
--
--   1. $\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1$.
--   2. $K\subseteq E$ is compact, convex, and has nonempty interior.
--   3. $V:E\to\mathbb R$ is continuous.
--   4. The push-forward of the tilted volume measure by $\nabla u$ equals the measure with density $1_K(p)\operatorname{ofReal}(e^{-V(p)})$.
--
--   Then
--   $$u\in C^1(E),$$
--   formalized as `ContDiff ℝ 1 u`.
--
--   This is the regularity conclusion used for the moment potential in the finite-dimensional compact-target setting.
--
--   **Formalization Note** The statement proves `ContDiff` of order $1$ on the whole finite-dimensional space; it does not state positive-definite Hessian, a global diffeomorphism, or a pointwise Monge–Ampère equation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_one_of_map_gradient
--       [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
--       {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
--       {V : E → ℝ} (hV : Continuous V)
--       (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
--         (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
--       ContDiff ℝ 1 u
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Selected supporting theorems: [`contDiff_one_of_convexOn_of_differentiable`](https://prove2.me/theorems/16eb9c9c-a99f-4109-be05-1626be515a47), [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760), [`eq_of_contact_of_sublevel_bounds`](https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270), [`exists_inverse_subgradient_volume_bounds`](https://prove2.me/theorems/d2723f7d-8cba-4654-bce4-6f99044af824), [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Previous: [`strictConvexOn_of_map_gradient`](https://prove2.me/theorems/2ec0713b-027d-49b5-9ef0-008413f11729).
--
--   [Source excerpt, lines 2156–2164](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L2156-L2164) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L2151-L2313 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.contDiff_one_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_readable
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    ContDiff ℝ 1 u := by sorry
