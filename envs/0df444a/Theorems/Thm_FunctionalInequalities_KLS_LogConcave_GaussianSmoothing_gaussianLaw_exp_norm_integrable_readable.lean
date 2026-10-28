-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:26.913017+00:00
-- url     : https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e
-- title:
--   Gaussian Exponential Norm Integrability
-- statement:
--   This is a moment estimate for the Gaussian law `gaussianLaw`.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $s\in\mathbb R$ satisfy $s>0$, and let $\gamma_s$ denote `gaussianLaw s`. Then
--
--   $$
--   \int_E e^{\|y\|}\,d\gamma_s(y)<\infty.
--   $$
--
--   Equivalently, $y\mapsto e^{\|y\|}$ is integrable with respect to $\gamma_s$. Completeness of $E$ is omitted from the declaration. This estimate supplies exponential integrability for Gaussian Laplace-transform and moment calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_exp_norm_integrable {s : ℝ} (hs : 0 < s) :
--       Integrable (fun y : E => Real.exp ‖y‖) (gaussianLaw s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Next: [`gaussianLaw_laplace`](https://prove2.me/theorems/1f27ed11-f52e-4f6b-b3d6-50fd828fde34).
--
--   [Source excerpt, lines 42–43](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L42-L43) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L40-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory ProbabilityTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : E => Real.exp ‖y‖) (gaussianLaw s) := by sorry
