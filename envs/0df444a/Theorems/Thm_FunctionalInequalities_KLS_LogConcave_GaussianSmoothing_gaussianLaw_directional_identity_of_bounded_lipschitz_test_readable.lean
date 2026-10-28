-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:55.667311+00:00
-- url     : https://prove2.me/theorems/123bb3a0-2332-4e67-a78a-7bf12553f53a
-- title:
--   Gaussian Directional Integration by Parts
-- statement:
--   This statement gives Gaussian integration by parts for bounded globally Lipschitz $C^1$ tests.
--
--   Let $n\in\mathbb N$, let $s>0$, let $f:\mathbb R^n\to\mathbb R$ be $C^1$ and globally Lipschitz with Lipschitz constant represented by `L : NNReal`, and suppose there is $C\in\mathbb R$ such that $\|f(x)\|\le C$ for every $x$. For every $v\in\mathbb R^n$, both functions $x\mapsto\langle x,v\rangle f(x)$ and $x\mapsto D_vf(x)$ are integrable with respect to `gaussianLaw s`, and
--
--   $$
--   \int \langle x,v\rangle f(x)\,d\gamma_s(x)
--   =
--   (2s)^{-1}\int D_vf(x)\,d\gamma_s(x).
--   $$
--
--   This is the directional Gaussian identity with the exact parameterization used by `gaussianLaw s`, valid in all finite dimensions including $n=0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_directional_identity_of_bounded_lipschitz_test {n : ℕ}
--       {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
--       (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith L f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       Integrable (fun x => ⟪x, v⟫ * f x) (gaussianLaw s) ∧
--       Integrable (fun x => fderiv ℝ f x v) (gaussianLaw s) ∧
--       (∫ x, ⟪x, v⟫ * f x ∂(gaussianLaw s)) =
--         (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂(gaussianLaw s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552), [`integral_eq_zero_of_integrable_weak_derivative`](https://prove2.me/theorems/4bbf5126-d256-459b-9474-606b9a141762), [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e).
--
--   Previous: [`smoothedLaw_norm_sq`](https://prove2.me/theorems/8855ba81-dd57-4aab-98f3-9959c375040d) · Next: [`gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/c0deab00-4b66-4ff2-9322-12a13e5f7645).
--
--   [Source excerpt, lines 409–416](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L409-L416) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L406-L478 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory Filter
open scoped ContDiff Topology RealInnerProductSpace
set_option maxHeartbeats 800000

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable {n : ℕ}
    {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith L f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ⟪x, v⟫ * f x) (gaussianLaw s) ∧
    Integrable (fun x => fderiv ℝ f x v) (gaussianLaw s) ∧
    (∫ x, ⟪x, v⟫ * f x ∂(gaussianLaw s)) =
      (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂(gaussianLaw s) := by sorry
