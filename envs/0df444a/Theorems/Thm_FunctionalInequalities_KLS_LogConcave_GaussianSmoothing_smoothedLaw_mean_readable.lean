-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_mean_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:44.3513+00:00
-- url     : https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154
-- title:
--   Gaussian Smoothing Preserves the Mean
-- statement:
--   This statement identifies the mean of a Gaussian-smoothed probability law.
--
--   Let $E$ be a finite-dimensional complete real inner-product space with its Borel measurable structure. Let $μ$ be a probability measure on $E$ with `MemLp id 2 μ`, meaning that the identity map has finite second moment. For $s>0$, let `smoothedLaw μ s` be the convolution with `gaussianLaw s`. Then
--
--   $$
--   \int_E y\,d(\operatorname{smoothedLaw}(μ,s))(y)
--   =
--   \int_E y\,dμ(y).
--   $$
--
--   This moment identity is useful when tracking centering through Gaussian regularization.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_mean (μ : Measure E) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
--       (∫ y : E, y ∂(smoothedLaw μ s)) = ∫ y : E, y ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`gaussianLaw_mean_zero`](https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337).
--
--   Previous: [`gaussianLaw_inner_sq`](https://prove2.me/theorems/a1a65a5b-0fa7-48a4-bd6f-576a0f2e068e) · Next: [`gaussianLaw_variance`](https://prove2.me/theorems/d32b8812-f3da-46ba-8045-625ae0264890).
--
--   [Source excerpt, lines 221–223](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L221-L223) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L220-L235 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(smoothedLaw μ s)) = ∫ y : E, y ∂μ := by sorry
