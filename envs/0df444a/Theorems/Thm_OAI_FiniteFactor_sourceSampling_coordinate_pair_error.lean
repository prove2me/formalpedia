-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceSampling_coordinate_pair_error
-- name    : OAI.FiniteFactor.sourceSampling_coordinate_pair_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:30:44.415536+00:00
-- url     : https://prove2.me/theorems/26fc485b-6371-4837-81f2-b3fb55030e94
-- title:
--   OAI.FiniteFactor.sourceSampling_coordinate_pair_error: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceSampling_coordinate_pair_error` of [lean/OAI/Analysis/FiniteFactor/OrbitSampling/PairMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/PairMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped Classical`):
--
--   ```lean
--   theorem sourceSampling_coordinate_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
--       (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
--       (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
--       (r b : Bool) (a c a' c' : ℝ) :
--       |(∫ s, ∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
--           (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n : ℝ)*θ i)) *
--           samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
--           (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw ∂unitIntervalMeasure) -
--         (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
--           (Set.Icc a c) (Set.Icc a' c') s ^ 2 ∂unitIntervalMeasure)| ≤
--         104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.samplingOrientedDensity`, `OAI.FiniteFactor.samplingOrientedWeight`, `OAI.FiniteFactor.sourceAngleLaw`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceSamplingCutoff`, `OAI.FiniteFactor.sourceSamplingPowers`, `OAI.FiniteFactor.sourceSamplingWidth` and `OAI.FiniteFactor.unitIntervalMeasure` (definitions bundle `OAIQ3Ff000` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.sourceSamplingSquaredError_ae` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/PairMoments.lean (declaration OAI.FiniteFactor.sourceSampling_coordinate_pair_error)

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

theorem sourceSampling_coordinate_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (r b : Bool) (a c a' c' : ℝ) :
    |(∫ s, ∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n : ℝ)*θ i)) *
        samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw ∂unitIntervalMeasure) -
      (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) (Set.Icc a' c') s ^ 2 ∂unitIntervalMeasure)| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  sorry

end
end FiniteFactor

end OAI
end
