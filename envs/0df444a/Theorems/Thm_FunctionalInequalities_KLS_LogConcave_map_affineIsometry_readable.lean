-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_map_affineIsometry_readable
-- name    : FunctionalInequalities.KLS.LogConcave.map_affineIsometry_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:15.547514+00:00
-- url     : https://prove2.me/theorems/24db795f-31a5-42d9-9329-a7272770b5c9
-- title:
--   Log-Concavity Under Affine Isometric Pushforward
-- statement:
--   This proves preservation of compact-set log-concavity under an affine isometric embedding.
--
--   Let $F$ and $E$ be real normed spaces with Borel measurable structures, assume $F$ is complete, and let $\nu$ be a log-concave probability measure on $F$. Let $\mu$ be a probability measure on $E$ and let $f:F\to E$ be an affine isometric embedding. If
--
--   $$\mu=f_\#\nu,$$
--
--   then $\mu$ is log-concave:
--
--   $$\operatorname{LogConcave}(\mu).$$
--
--   The conclusion allows the image of $f$ to be lower-dimensional and requires no density assumption. This provides the affine-isometric transport direction for the library's compact-set definition of log-concavity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem map_affineIsometry [CompleteSpace F]
--       (ν : ProbabilityMeasure F) (hν : LogConcave ν)
--       (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
--       (hmap : (μ : Measure E) = (ν : Measure F).map f) :
--       LogConcave μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Transport`](https://prove2.me/theorems/e2b06803-5a96-41cf-bc8d-6b89b02cb255).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Next: [`cond`](https://prove2.me/theorems/a9c544d7-ce6e-4338-89f4-f44a4207b027).
--
--   [Source excerpt, lines 66–70](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L66-L70) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L64-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Transport`, declaration `FunctionalInequalities.KLS.LogConcave.map_affineIsometry`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport

open MeasureTheory Set Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem FunctionalInequalities.KLS.LogConcave.map_affineIsometry_readable [CompleteSpace F]
    (ν : ProbabilityMeasure F) (hν : LogConcave ν)
    (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
    (hmap : (μ : Measure E) = (ν : Measure F).map f) :
    LogConcave μ := by sorry
