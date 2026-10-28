-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_row_joint_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.row_joint_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:32.974109+00:00
-- url     : https://prove2.me/theorems/23822530-689b-4fdf-a9f4-e7013d658d1f
-- title:
--   Joint Convergence of Gaussian Approximation Rows
-- statement:
--   This is the fixed-row convergence statement for the regular Gaussian-then-quadratic approximation.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be a probability measure with finite second moment, and fix $n\in\mathbb N$. Let `rowLaw μ n k` be the $k$th law in row $n$, and let `statistics` collect its associated statistics. Then
--
--   $$
--   \bigl(\operatorname{rowLaw}(\mu,n,k),\operatorname{statistics}(\operatorname{rowLaw}(\mu,n,k))\bigr)
--   \longrightarrow
--   \bigl(\operatorname{gaussianSeq}(\mu,n),\operatorname{statistics}(\operatorname{gaussianSeq}(\mu,n))\bigr)
--   $$
--
--   as $k\to\infty$. The convergence is in the product topology encoded by `Tendsto` and combines convergence of the law with convergence of the recorded statistics. It is stated row by row and does not assert the diagonal approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem row_joint_tendsto (μ : ProbabilityMeasure E) (hμ2 : MemLp id 2 (μ : Measure E)) (n : ℕ) :
--       Tendsto (fun k : ℕ => (rowLaw μ n k, statistics (rowLaw μ n k)))
--         atTop (𝓝 (gaussianSeq μ n, statistics (gaussianSeq μ n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation`](https://prove2.me/theorems/eabcdc52-c914-4c59-b1af-3d43455f910d).
--
--   Supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`covariance_quadraticTilt_tendsto`](https://prove2.me/theorems/34f101b3-ed51-49ba-ad65-9df453ba5bd4), [`integral_quadraticTilt_tendsto`](https://prove2.me/theorems/ffe92b60-eb22-4bf2-b690-535d392b8556).
--
--   [Source excerpt, lines 75–77](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation.lean#L75-L77) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation.lean#L74-L90 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.row_joint_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.row_joint_tendsto_readable (μ : ProbabilityMeasure E) (hμ2 : MemLp id 2 (μ : Measure E)) (n : ℕ) :
    Tendsto (fun k : ℕ => (rowLaw μ n k, statistics (rowLaw μ n k)))
      atTop (𝓝 (gaussianSeq μ n, statistics (gaussianSeq μ n))) := by sorry
