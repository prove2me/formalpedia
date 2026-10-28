-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceSampling_mass_limit_event
-- name    : OAI.FiniteFactor.sourceSampling_mass_limit_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:30:59.562102+00:00
-- url     : https://prove2.me/theorems/55b49818-5c29-4ecb-ae3d-65d0cd412364
-- title:
--   OAI.FiniteFactor.sourceSampling_mass_limit_event: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceSampling_mass_limit_event` of [lean/OAI/Analysis/FiniteFactor/OrbitSampling/Cube.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/Cube.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter Finset`, `open scoped Classical ENNReal Topology`):
--
--   ```lean
--   theorem sourceSampling_mass_limit_event : ∀ᵐ θ ∂sourceAngleLaw,
--       ∀ I : Finset SourceCoordinate,
--         Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
--           atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal))
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.sourceAngleLaw`, `OAI.FiniteFactor.sourceSamplingLambda` and `OAI.FiniteFactor.sourceSamplingUntrimmed` (definitions bundle `OAIQ3Ff000` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.exists_source_prepared_finite` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/Cube.lean (declaration OAI.FiniteFactor.sourceSampling_mass_limit_event)

import Mathlib
import Definitions.Def_OAIQ3Ff000

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSampling_mass_limit_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
        atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal)) := by
  sorry

end
end FiniteFactor

end OAI
end
