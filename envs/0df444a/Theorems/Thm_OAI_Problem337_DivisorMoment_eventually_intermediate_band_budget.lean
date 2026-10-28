-- Prove2me | Theorems.Thm_OAI_Problem337_DivisorMoment_eventually_intermediate_band_budget
-- name    : OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:02:35.060816+00:00
-- url     : https://prove2.me/theorems/8ebfe26b-5622-4610-9fae-627f1ddda90b
-- title:
--   OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget: intermediate lemma from OpenAI, Short Egyptian fractions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget` of [lean/OAI/NumberTheory/EgyptianFractions/IntermediateBandBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/IntermediateBandBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem337.DivisorMoment`, with `open Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem eventually_intermediate_band_budget (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
--       ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N j : ℕ),
--         S / (2 * Real.log S) ≤ v → v ≤ D * S →
--         Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
--         (N : ℝ) ≤ Real.exp (D * S) →
--         4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ) →
--         (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
--           (fun h => DivisorClasses.BandClass (N + h) S v Y j),
--           (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ 2 * Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem337.truncatedDivisorCount` and `OAI.Problem337.DivisorClasses.BandClass` (definitions bundle `OAIQ8EF000` of this split).
--
--   **Used by.** The proof of `OAI.Problem337.eventually_residue_level_moment` of this split imports it.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/IntermediateBandBudget.lean (declaration OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget)

import Mathlib
import Definitions.Def_OAIQ8EF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Filter
open scoped Topology BigOperators

namespace Problem337.DivisorMoment
attribute [local instance] Classical.propDecidable

theorem eventually_intermediate_band_budget (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N j : ℕ),
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      (N : ℝ) ≤ Real.exp (D * S) →
      4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.BandClass (N + h) S v Y j),
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ 2 * Y := by
  sorry

end Problem337.DivisorMoment

end OAI
end
