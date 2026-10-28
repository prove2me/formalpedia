-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_map_gradient_readable
-- name    : FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:58.588673+00:00
-- url     : https://prove2.me/theorems/8a48698f-79ec-4b96-966b-75b5ba3d4373
-- title:
--   Centered Difference Bound for Moment-Map Potentials
-- statement:
--   This formalizes the centered-difference estimate associated with regularity of the moment map, cited in Lemma 2.2 of Letwin (arXiv:2607.24164v1) (Klartag [41]).
--
--   Let $u,V:\mathbb R^n\to\mathbb R$, let $L\in[0,\infty)$, and assume:
--
--   1. $u$ is $L$-Lipschitz and convex;
--   2. $\int e^{-u(x)}\,dx=1$;
--   3. $K\subset\mathbb R^n$ is compact and convex;
--   4. $V$ is $C^1$ and $V(y)-\frac\kappa2\|y\|^2$ is convex for some $\kappa>0$;
--   5. the pushforward of the tilted volume measure with density $e^{-u}$ under $\nabla u$ equals the measure with density $e^{-V}$ on $K$;
--   6. $u$ is $C^1$.
--
--   Then, for every $x,h\in\mathbb R^n$,
--
--   $$
--   u_h^2u(x):=u(x+h)+u(x-h)-2u(x)
--   \leq \frac{4}{\kappa}\|h\|^2.
--   $$
--
--   This exports the exact coefficient used in the subsequent Lipschitz-gradient regularity argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem secondDifference_le_of_map_gradient {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
--       {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
--       (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
--       {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
--       (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
--       (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
--       (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
--         (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
--           (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
--       (hC1 : ContDiff ℝ 1 u) :
--       ∀ x h : EuclideanSpace ℝ (Fin n),
--         u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/GradientLipschitz`](https://prove2.me/theorems/b5069800-f62d-405b-8e8b-6b9408cea016).
--
--   Selected supporting theorems: [`ae_exists_quadraticAt_expansion`](https://prove2.me/theorems/995efd14-b691-40e5-adc5-c0effdf385d3), [`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`](https://prove2.me/theorems/d27371ec-adba-4761-8a3a-e229679243d0), [`exists_penalized_maximum_with_comparison`](https://prove2.me/theorems/511a8bb6-640f-477b-98fa-7c8e07f3450e), [`posDef_and_convolution_le_log_det_hessianMatrix`](https://prove2.me/theorems/6d69beca-a1f9-48e2-959c-68716a21a551), [`posDef_and_det_eq_of_quadratic_expansion`](https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b).
--
--   [Source excerpt, lines 89–100](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean#L89-L100) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean#L88-L174 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.GradientLipschitz`, declaration `FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz

open MeasureTheory Set Metric Filter

theorem FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_readable {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by sorry
