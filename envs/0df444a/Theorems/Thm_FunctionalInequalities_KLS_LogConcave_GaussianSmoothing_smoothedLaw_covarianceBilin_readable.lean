-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_covarianceBilin_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covarianceBilin_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:27.156346+00:00
-- url     : https://prove2.me/theorems/c357a868-1434-4039-b92d-a0210d64482e
-- title:
--   Smoothed Covariance Bilinear Form
-- statement:
--   This is the covariance-bilinear-form identity for Gaussian smoothing.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure. Let $\mu$ be a probability measure with finite second moment, let $s>0$, and let $v,w\in E$. For the smoothed law `smoothedLaw μ s`,
--
--   $$
--   \operatorname{CovBilin}_{\mu*\gamma_s}(v,w)
--   =\operatorname{CovBilin}_{\mu}(v,w)+\frac{\langle v,w\rangle}{2s}.
--   $$
--
--   Equivalently, Gaussian smoothing adds $(2s)^{-1}$ times the ambient inner product to the covariance bilinear form. The declaration does not reformulate this as an operator equality, although it determines the corresponding quadratic covariance operator.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_covarianceBilin (μ : Measure E) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v w : E) :
--       covarianceBilin (smoothedLaw μ s) v w = covarianceBilin μ v w + ⟪v, w⟫ / (2 * s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`smoothedLaw_variance`](https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5).
--
--   Previous: [`smoothedLaw_variance`](https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5) · Next: [`smoothedLaw_inner_sq`](https://prove2.me/theorems/e994f4a0-91dd-45b0-a526-8baeb50d6e6b).
--
--   [Source excerpt, lines 275–277](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L275-L277) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L274-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covarianceBilin`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covarianceBilin_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v w : E) :
    covarianceBilin (smoothedLaw μ s) v w = covarianceBilin μ v w + ⟪v, w⟫ / (2 * s) := by sorry
