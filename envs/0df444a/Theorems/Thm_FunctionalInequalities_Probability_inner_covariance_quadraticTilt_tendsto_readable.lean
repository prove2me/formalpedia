-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_inner_covariance_quadraticTilt_tendsto_readable
-- name    : FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:43.088545+00:00
-- url     : https://prove2.me/theorems/ce081f02-1f45-416f-82f0-2ad61ab09ec7
-- title:
--   Pointwise Covariance Convergence Under Tilting
-- statement:
--   This is the scalar covariance convergence statement for small quadratic tilts.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be a probability measure with finite second moment, expressed as `MemLp id 2 μ`, and let $u,v\in E$. For the tilted probability measure with weight $e^{-\delta\|x\|^2/2}$,
--
--   $$
--   \left\langle \operatorname{Cov}(\mu_\delta)u,v\right\rangle
--   \longrightarrow
--   \left\langle \operatorname{Cov}(\mu)u,v\right\rangle
--   \qquad(\delta\to0^+).
--   $$
--
--   The convergence is in $\mathbb R$ along the one-sided neighborhood of zero. This scalar form is the ingredient used to establish operator-norm covariance convergence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_covariance_quadraticTilt_tendsto (μ : ProbabilityMeasure E)
--       (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) (u v : E) :
--       Tendsto (fun δ : ℝ => ⟪Covariance.operator
--         ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) u, v⟫)
--         (𝓝[>] (0 : ℝ)) (𝓝 ⟪Covariance.operator (μ : Measure E) u, v⟫)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/QuadraticTilt`](https://prove2.me/theorems/60d2b9ef-6970-4c75-8c09-768a09afafb4).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Supporting theorems: [`integral_quadraticTilt_tendsto`](https://prove2.me/theorems/ffe92b60-eb22-4bf2-b690-535d392b8556).
--
--   Previous: [`integral_quadraticTilt_tendsto`](https://prove2.me/theorems/ffe92b60-eb22-4bf2-b690-535d392b8556) · Next: [`covariance_quadraticTilt_tendsto`](https://prove2.me/theorems/34f101b3-ed51-49ba-ad65-9df453ba5bd4).
--
--   [Source excerpt, lines 188–192](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L188-L192) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L187-L214 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, declaration `FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_readable (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) (u v : E) :
    Tendsto (fun δ : ℝ => ⟪Covariance.operator
      ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) u, v⟫)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪Covariance.operator (μ : Measure E) u, v⟫) := by sorry
