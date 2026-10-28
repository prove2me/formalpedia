-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_logConcave_of_concave_tilt_readable
-- name    : FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:47.13679+00:00
-- url     : https://prove2.me/theorems/ec28e166-3e80-4482-a015-77d8598725bc
-- title:
--   Concave Tilting Preserves Log-Concavity
-- statement:
--   This statement asserts that a continuous concave tilt of a log-concave probability law remains log-concave.
--
--   Let $E$ be a finite-dimensional real inner-product normed space equipped with its Borel measurable structure, and let $μ$ and $ν$ be probability measures on $E$. Assume:
--
--   1. $μ$ is log-concave.
--   2. $φ : E → ℝ$ is continuous.
--   3. $φ$ is concave on all of $E$.
--   4. As measures on $E$, $ν$ equals the tilt of $μ$ by $φ$, expressed in Lean by `Measure.tilted`:
--
--   $$ν = \operatorname{tilted}(μ,φ).$$
--
--   Then $ν$ is log-concave:
--
--   $$ν\text{ is log-concave}.$$
--
--   The result is useful for transporting log-concavity through exponential weights, including laws supported on proper affine subspaces and the zero-dimensional case.
--
--   **Formalization Note** The log-concavity predicate is `KLS.LogConcave`. The statement imposes finite dimensionality but no positive-dimension assumption, and the equality of measures is interpreted through the canonical coercions from probability measures to measures.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem logConcave_of_concave_tilt (μ ν : ProbabilityMeasure E) (hLC : KLS.LogConcave μ)
--       (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
--       (hν : (ν : Measure E) = (μ : Measure E).tilted φ) : KLS.LogConcave ν
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/ConcaveTilt`](https://prove2.me/theorems/7ed5056e-c3f4-4ab8-9bf8-55101609725f).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70), [`isBorellDensity_of_concave_tilt`](https://prove2.me/theorems/74db6db5-1902-4308-9adf-57a1e7cc376f), [`map_affineIsometry`](https://prove2.me/theorems/24db795f-31a5-42d9-9329-a7272770b5c9), [`affineSupport_intrinsicMeasure`](https://prove2.me/theorems/69034b90-b400-423d-8cf5-e41038da0be1).
--
--   Previous: [`isBorellDensity_of_concave_tilt`](https://prove2.me/theorems/74db6db5-1902-4308-9adf-57a1e7cc376f).
--
--   [Source excerpt, lines 81–83](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/ConcaveTilt.lean#L81-L83) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/ConcaveTilt.lean#L79-L105 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt`, declaration `FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_ConcaveTilt

open MeasureTheory Set Filter Topology FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt_readable (μ ν : ProbabilityMeasure E) (hLC : KLS.LogConcave μ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) : KLS.LogConcave ν := by sorry
