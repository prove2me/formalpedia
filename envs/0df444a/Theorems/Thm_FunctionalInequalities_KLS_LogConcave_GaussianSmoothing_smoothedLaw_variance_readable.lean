-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_variance_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:31.6699+00:00
-- url     : https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5
-- title:
--   Variance Addition Under Gaussian Smoothing
-- statement:
--   This is the variance-addition identity for Gaussian smoothing.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure. Let $\mu$ be a probability measure on $E$ with finite second moment, let $s>0$, and let $v\in E$. For `smoothedLaw μ s`, obtained by convolving $\mu$ with `gaussianLaw s`,
--
--   $$
--   \operatorname{Var}_{\mu*\gamma_s}\langle v,\cdot\rangle
--   =\operatorname{Var}_{\mu}\langle v,\cdot\rangle
--   +\frac{\|v\|^2}{2s}.
--   $$
--
--   The result records the exact contribution of the independent Gaussian noise. The finite-second-moment assumption is expressed as `MemLp id 2 μ`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothedLaw_variance (μ : Measure E) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
--       variance (fun y : E => ⟪v, y⟫) (smoothedLaw μ s) =
--         variance (fun y : E => ⟪v, y⟫) μ + ‖v‖ ^ 2 / (2 * s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`gaussianLaw_variance`](https://prove2.me/theorems/d32b8812-f3da-46ba-8045-625ae0264890).
--
--   Previous: [`gaussianLaw_variance`](https://prove2.me/theorems/d32b8812-f3da-46ba-8045-625ae0264890) · Next: [`smoothedLaw_covarianceBilin`](https://prove2.me/theorems/c357a868-1434-4039-b92d-a0210d64482e).
--
--   [Source excerpt, lines 256–259](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L256-L259) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L255-L271 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_variance_readable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (smoothedLaw μ s) =
      variance (fun y : E => ⟪v, y⟫) μ + ‖v‖ ^ 2 / (2 * s) := by sorry
