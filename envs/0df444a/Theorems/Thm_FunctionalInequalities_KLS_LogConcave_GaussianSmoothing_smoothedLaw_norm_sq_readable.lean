-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_norm_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:43.788273+00:00
-- url     : https://prove2.me/theorems/8855ba81-dd57-4aab-98f3-9959c375040d
-- title:
--   Squared-Norm Moment Under Gaussian Smoothing
-- statement:
--   This statement gives the exact change in the squared-norm moment under Gaussian smoothing.
--
--   Let $E$ be a finite-dimensional complete real inner-product space with its Borel measurable structure. Let $μ$ be a probability measure on $E$ with finite second moment, expressed as `MemLp id 2 μ`. Let $s>0$. Then
--
--   $$
--   \int_E \|y\|^2\,d(\operatorname{smoothedLaw}(μ,s))(y)
--   =
--   \int_E \|y\|^2\,dμ(y)
--   +\frac{\operatorname{finrank}_{\mathbb R}E}{2s}.
--   $$
--
--   The theorem records the dimension-dependent increase in the total second moment caused by the Gaussian noise.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
--       (∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) =
--         (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`smoothedLaw_inner_sq`](https://prove2.me/theorems/e994f4a0-91dd-45b0-a526-8baeb50d6e6b).
--
--   Previous: [`smoothedLaw_inner_sq`](https://prove2.me/theorems/e994f4a0-91dd-45b0-a526-8baeb50d6e6b) · Next: [`gaussianLaw_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/123bb3a0-2332-4e67-a78a-7bf12553f53a).
--
--   [Source excerpt, lines 332–335](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L332-L335) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L331-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s) := by sorry
