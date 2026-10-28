-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_mean_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:50.247319+00:00
-- url     : https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337
-- title:
--   Gaussian Law Has Zero Mean
-- statement:
--   This is the mean-zero identity for `gaussianLaw`.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure, let $s>0$, and let $\gamma_s=\texttt{gaussianLaw }s$. Then
--
--   $$
--   \int_E y\,d\gamma_s(y)=0_E.
--   $$
--
--   The conclusion is vector-valued and uses the Bochner integral. This is a basic symmetry property of the Gaussian noise and is used in the covariance and smoothing calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_mean_zero {s : ℝ} (hs : 0 < s) :
--       (∫ y : E, y ∂(gaussianLaw s)) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`gaussianLaw_laplace`](https://prove2.me/theorems/1f27ed11-f52e-4f6b-b3d6-50fd828fde34).
--
--   Previous: [`gaussianLaw_laplace`](https://prove2.me/theorems/1f27ed11-f52e-4f6b-b3d6-50fd828fde34) · Next: [`gaussianLaw_inner_sq`](https://prove2.me/theorems/a1a65a5b-0fa7-48a4-bd6f-576a0f2e068e).
--
--   [Source excerpt, lines 137–138](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L137-L138) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L136-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(gaussianLaw s)) = 0 := by sorry
