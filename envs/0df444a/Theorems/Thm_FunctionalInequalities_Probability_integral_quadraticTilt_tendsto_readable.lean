-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_quadraticTilt_tendsto_readable
-- name    : FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:45.389162+00:00
-- url     : https://prove2.me/theorems/ffe92b60-eb22-4bf2-b690-535d392b8556
-- title:
--   Convergence of Small Quadratic Tilts
-- statement:
--   This formalizes the normalized small-quadratic-tilt convergence described in the source module for the regular approximation of Bizeul–Klartag–Lehec (arXiv:2610.05474v1, Section 2, p. 5).
--
--   Let $E$ be a Borel real normed space, let $F$ be a complete real normed space, let $\mu$ be a probability measure on $E$, let $f:E\to F$ be integrable with respect to $\mu$, and for $\delta\in\mathbb R$ define the tilted measure by the weight $e^{-\delta\|x\|^2/2}$. As $\delta\to0^+$,
--
--   $$
--   \int f(x)\,d\bigl(\mu.\operatorname{tilted}(x\mapsto-\tfrac\delta2\|x\|^2)\bigr)(x)
--   \longrightarrow \int f(x)\,d\mu(x).
--   $$
--
--   The limit is in the norm topology of $F$ and is taken through positive $\delta$. Only probability and integrability are assumed; no moment or log-concavity hypothesis is added.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_quadraticTilt_tendsto {E F : Type*} [NormedAddCommGroup E]
--       [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
--       [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
--       (μ : Measure E) [IsProbabilityMeasure μ] (f : E → F) (hf : Integrable f μ) :
--       Tendsto
--         (fun δ : ℝ => ∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
--         (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/QuadraticTilt`](https://prove2.me/theorems/60d2b9ef-6970-4c75-8c09-768a09afafb4).
--
--   Next: [`inner_covariance_quadraticTilt_tendsto`](https://prove2.me/theorems/ce081f02-1f45-416f-82f0-2ad61ab09ec7).
--
--   [Source excerpt, lines 28–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L28-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L26-L90 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, declaration `FunctionalInequalities.Probability.integral_quadraticTilt_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt

open MeasureTheory Filter Topology Set

theorem FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_readable {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → F) (hf : Integrable f μ) :
    Tendsto
      (fun δ : ℝ => ∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by sorry
