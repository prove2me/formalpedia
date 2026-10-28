-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:55.099552+00:00
-- url     : https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d
-- title:
--   Convexity from a Nonnegative Hessian Lower Bound
-- statement:
--   This is the standard convexity implication from a pointwise Hessian lower bound.
--
--   Let $E$ be a real inner-product space and let $U:E\to\mathbb R$ be $C^2$. Let $\rho\geq0$ and suppose that for every $x,v\in E$,
--
--   $$
--   \rho\,\|v\|^2\leq D^2U(x)(v,v).
--   $$
--
--   Then $U$ is convex on all of $E$:
--
--   $$
--   U\text{ is convex on }E.
--   $$
--
--   The Hessian is represented by `bilinearIteratedFDerivTwo`, and no completeness or finite-dimensionality assumption is required. The result may be used to convert curvature-type Hessian hypotheses into global convexity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convexOn_of_hessian_ge {U : E → ℝ} (hU : ContDiff ℝ 2 U) {ρ : ℝ} (hρ : 0 ≤ ρ)
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
--       ConvexOn ℝ Set.univ U
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Next: [`integrable_weightedLaplacian_gamma`](https://prove2.me/theorems/59b753c1-8f58-4542-b8fb-6fd46908e479).
--
--   [Source excerpt, lines 39–41](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L39-L41) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L37-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge_readable {U : E → ℝ} (hU : ContDiff ℝ 2 U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ConvexOn ℝ Set.univ U := by sorry
