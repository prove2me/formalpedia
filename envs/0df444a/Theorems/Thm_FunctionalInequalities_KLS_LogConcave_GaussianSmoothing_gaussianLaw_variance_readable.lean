-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_variance_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:27.211606+00:00
-- url     : https://prove2.me/theorems/d32b8812-f3da-46ba-8045-625ae0264890
-- title:
--   Gaussian Linear Variance
-- statement:
--   This is the variance formula for linear observables of `gaussianLaw`.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure, let $s>0$, and let $v\in E$. For the linear observable $y\mapsto\langle v,y\rangle$ and $\gamma_s=\texttt{gaussianLaw }s$,
--
--   $$
--   \operatorname{Var}_{\gamma_s}\langle v,\cdot\rangle
--   =\frac{\|v\|^2}{2s}.
--   $$
--
--   The declaration includes the required completeness, finite-dimensionality, and Borel assumptions. It identifies the variance parameter used by the Gaussian smoothing construction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_variance {s : ℝ} (hs : 0 < s) (v : E) :
--       variance (fun y : E => ⟪v, y⟫) (gaussianLaw s) = ‖v‖ ^ 2 / (2 * s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`gaussianLaw_inner_sq`](https://prove2.me/theorems/a1a65a5b-0fa7-48a4-bd6f-576a0f2e068e), [`gaussianLaw_mean_zero`](https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337).
--
--   Previous: [`smoothedLaw_mean`](https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154) · Next: [`smoothedLaw_variance`](https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5).
--
--   [Source excerpt, lines 238–239](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L238-L239) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L237-L253 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance_readable {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (gaussianLaw s) = ‖v‖ ^ 2 / (2 * s) := by sorry
