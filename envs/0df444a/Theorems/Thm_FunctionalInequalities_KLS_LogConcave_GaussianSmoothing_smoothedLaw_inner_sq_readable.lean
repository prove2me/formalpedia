-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_inner_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_inner_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:47.252582+00:00
-- url     : https://prove2.me/theorems/e994f4a0-91dd-45b0-a526-8baeb50d6e6b
-- title:
--   Directional Second Moment Under Gaussian Smoothing
-- statement:
--   This statement gives the exact change in a directional second moment under Gaussian smoothing.
--
--   Let $E$ be a finite-dimensional complete real inner-product space with its Borel measurable structure. Let $μ$ be a probability measure on $E$ with finite second moment, expressed as `MemLp id 2 μ`. Let $s>0$ and let $v\in E$. Then
--
--   $$
--   \int_E \langle v,y\rangle^2\,d(\operatorname{smoothedLaw}(μ,s))(y)
--   =
--   \int_E \langle v,y\rangle^2\,dμ(y)
--   +\frac{\|v\|^2}{2s}.
--   $$
--
--   This is the directional raw second-moment formula for the Gaussian noise used in regular approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_inner_sq (μ : Measure E) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
--       (∫ y : E, ⟪v, y⟫ ^ 2 ∂(smoothedLaw μ s)) =
--         (∫ y : E, ⟪v, y⟫ ^ 2 ∂μ) + ‖v‖ ^ 2 / (2 * s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`smoothedLaw_mean`](https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154), [`smoothedLaw_variance`](https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5).
--
--   Previous: [`smoothedLaw_covarianceBilin`](https://prove2.me/theorems/c357a868-1434-4039-b92d-a0210d64482e) · Next: [`smoothedLaw_norm_sq`](https://prove2.me/theorems/8855ba81-dd57-4aab-98f3-9959c375040d).
--
--   [Source excerpt, lines 310–313](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L310-L313) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L309-L329 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_inner_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_inner_sq_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ⟪v, y⟫ ^ 2 ∂μ) + ‖v‖ ^ 2 / (2 * s) := by sorry
