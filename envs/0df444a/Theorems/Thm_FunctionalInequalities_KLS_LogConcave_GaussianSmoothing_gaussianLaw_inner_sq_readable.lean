-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_inner_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:18.819994+00:00
-- url     : https://prove2.me/theorems/a1a65a5b-0fa7-48a4-bd6f-576a0f2e068e
-- title:
--   Gaussian Inner-Product Second Moment
-- statement:
--   This is the second-moment formula for the Gaussian law `gaussianLaw`.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $s>0$, and let $v\in E$. Then
--
--   $$
--   \int_E\langle v,y\rangle^2\,d\gamma_s(y)
--   =\frac{\|v\|^2}{2s}.
--   $$
--
--   The result uses the Gaussian normalization encoded by `gaussianLaw`; completeness of $E$ is not required in the type. It is the raw second-moment identity from which the Gaussian variance formula follows.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_inner_sq {s : ℝ} (hs : 0 < s) (v : E) :
--       (∫ y : E, ⟪v, y⟫ ^ 2 ∂(gaussianLaw s)) = ‖v‖ ^ 2 / (2 * s)
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
--   Previous: [`gaussianLaw_mean_zero`](https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337) · Next: [`smoothedLaw_mean`](https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154).
--
--   [Source excerpt, lines 166–167](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L166-L167) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L164-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(gaussianLaw s)) = ‖v‖ ^ 2 / (2 * s) := by sorry
