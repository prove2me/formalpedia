-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceSampling_second_pair_error
-- name    : OAI.FiniteFactor.sourceSampling_second_pair_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:40:35.835898+00:00
-- url     : https://prove2.me/theorems/e2369df1-b615-4c4a-a4bd-1273428a6da4
-- title:
--   OAI.FiniteFactor.sourceSampling_second_pair_error: intermediate lemma from OpenAI, Backward intertwiners and a transitive commutant
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Hyperinvariant.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Backward intertwiners and a transitive commutant*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceSampling_second_pair_error` of [lean/OAI/Analysis/FiniteFactor/OrbitSampling/SecondCorrelation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/SecondCorrelation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped Classical`):
--
--   ```lean
--   theorem sourceSampling_second_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
--       (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
--       (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
--       (G : Set ℝ) (hG : MeasurableSet G) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
--       |(∫ θ, samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
--           (Set.Icc a c) G s (Int.fract ((n : ℝ)*θ i)) *
--           samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
--           (Set.Icc a c) G s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
--         samplingTestedSecondDensity (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (Set.Icc a c) G s ^ 2| ≤
--         104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.samplingTestedSecondDensity`, `OAI.FiniteFactor.samplingTestedSecondWeight`, `OAI.FiniteFactor.sourceAngleLaw`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceSamplingCutoff`, `OAI.FiniteFactor.sourceSamplingPowers` and `OAI.FiniteFactor.sourceSamplingWidth` (definitions bundle `OAIQ3Ff000` of this split).
--
--   **Used by.** The proof of `OAI_FiniteFactor_sourceSampling_coordinate_pair_error` of this split imports it.
-- source:
--   OpenAI, Backward intertwiners and a transitive commutant, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/SecondCorrelation.lean (declaration OAI.FiniteFactor.sourceSampling_second_pair_error)

import Mathlib
import Definitions.Def_OAIQ3Ff000

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

theorem sourceSampling_second_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (G : Set ℝ) (hG : MeasurableSet G) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ θ, samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n : ℝ)*θ i)) *
        samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingTestedSecondDensity (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (Set.Icc a c) G s ^ 2| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  sorry

end
end FiniteFactor

end OAI
end
