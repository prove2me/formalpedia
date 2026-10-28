-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_laplace_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:33.417452+00:00
-- url     : https://prove2.me/theorems/1f27ed11-f52e-4f6b-b3d6-50fd828fde34
-- title:
--   Gaussian Law Laplace Transform
-- statement:
--   This is the Laplace-transform formula for the Gaussian law `gaussianLaw`.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $s>0$, and let $z\in E$. Then
--
--   $$
--   \int_E e^{\langle z,y\rangle}\,d\gamma_s(y)
--   =\exp\left(\frac{\|z\|^2}{4s}\right),
--   $$
--
--   where $\gamma_s=\texttt{gaussianLaw }s$. Completeness of $E$ is not required by the declaration. The formula identifies the normalization used for the Gaussian smoothing and supports the subsequent moment identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_laplace {s : ℝ} (hs : 0 < s) (z : E) :
--       (∫ y, Real.exp ⟪z, y⟫ ∂(gaussianLaw (V := E) s)) = Real.exp (‖z‖ ^ 2 / (4 * s))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Previous: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e) · Next: [`gaussianLaw_mean_zero`](https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337).
--
--   [Source excerpt, lines 79–80](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L79-L80) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L77-L105 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_readable {s : ℝ} (hs : 0 < s) (z : E) :
    (∫ y, Real.exp ⟪z, y⟫ ∂(gaussianLaw (V := E) s)) = Real.exp (‖z‖ ^ 2 / (4 * s)) := by sorry
