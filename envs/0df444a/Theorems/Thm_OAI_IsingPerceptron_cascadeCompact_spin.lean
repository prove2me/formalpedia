-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_cascadeCompact_spin
-- name    : OAI.IsingPerceptron.cascadeCompact_spin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:14.999047+00:00
-- url     : https://prove2.me/theorems/25b28605-3119-4dc3-9819-d8bf2e440cdf
-- title:
--   OAI.IsingPerceptron.cascadeCompact_spin: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.cascadeCompact_spin` of [lean/OAI/Probability/IsingPerceptron/CascadeFreshMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/CascadeFreshMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal Classical`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal Classical`):
--
--   ```lean
--   lemma cascadeCompact_spin (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
--       (σ : ℕ → LabeledLeaf n) :
--       spinArray (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) =
--         diagonalPatch 1 (cascadeScalarArray n a σ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.RealArray`, `OAI.IsingPerceptron.cascadeScalarArray`, `OAI.IsingPerceptron.compactScalarArray`, `OAI.IsingPerceptron.diagonalPatch` and `OAI.IsingPerceptron.spinArray` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_cascade_spin_block_tendsto`, `OAI.InvariantIsing.cavity_finite_compact_block`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match`, `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match` and `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/CascadeFreshMoments.lean (declaration OAI.IsingPerceptron.cascadeCompact_spin)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma cascadeCompact_spin (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) :
    spinArray (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) =
      diagonalPatch 1 (cascadeScalarArray n a σ) := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix

end

end OAI
end
