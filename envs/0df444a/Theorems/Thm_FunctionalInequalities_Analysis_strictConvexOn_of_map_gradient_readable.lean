-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_map_gradient_readable
-- name    : FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:59.268638+00:00
-- url     : https://prove2.me/theorems/2ec0713b-027d-49b5-9ef0-008413f11729
-- title:
--   Strict Convexity From Compact Target Push-Forward
-- statement:
--   This states strict convexity of a moment potential under a compact-target push-forward hypothesis.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume
--   $$\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1.$$
--   Let $K\subseteq E$ be compact, convex, and nonempty. Let $V:E\to\mathbb R$ be continuous. Assume that the push-forward of the tilted volume measure by $\nabla u$ equals the volume measure with density $1_K(p)\operatorname{ofReal}(e^{-V(p)})$. Then
--   $$u\text{ is strictly convex on }E.$$
--
--   The result packages the contact-set argument into a global strict-convexity conclusion. It does not assert differentiability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem strictConvexOn_of_map_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
--       {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
--       {V : E → ℝ} (hV : Continuous V)
--       (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
--         (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
--       StrictConvexOn ℝ univ u
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`eq_of_contact_of_sublevel_bounds`](https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270), [`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`](https://prove2.me/theorems/d27371ec-adba-4761-8a3a-e229679243d0), [`strictConvexOn_of_contact_eq`](https://prove2.me/theorems/6e139777-147e-446b-9423-99da9a6d9b75), [`volume_subgradientImage_eq_lintegral_of_isOpen`](https://prove2.me/theorems/a875c8d6-d13c-4184-b1ba-d8541c085171).
--
--   Previous: [`eq_of_contact_of_sublevel_bounds`](https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270) · Next: [`contDiff_one_of_map_gradient`](https://prove2.me/theorems/0ffece2e-a383-4c75-b592-04da65ab3fa7).
--
--   [Source excerpt, lines 1987–1995](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1987-L1995) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1984-L2087 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric

theorem FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_readable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    StrictConvexOn ℝ univ u := by sorry
