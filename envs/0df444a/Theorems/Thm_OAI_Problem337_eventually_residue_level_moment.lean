-- Prove2me | Theorems.Thm_OAI_Problem337_eventually_residue_level_moment
-- name    : OAI.Problem337.eventually_residue_level_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:40.504395+00:00
-- url     : https://prove2.me/theorems/34d2edc3-746c-4887-9acd-d60fc95b701b
-- title:
--   OAI.Problem337.eventually_residue_level_moment: intermediate lemma from OpenAI, Short Egyptian fractions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem337.eventually_residue_level_moment` of [lean/OAI/NumberTheory/EgyptianFractions/DensityMomentBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/DensityMomentBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem337`, with `open scoped BigOperators`, `open Filter`):
--
--   ```lean
--   theorem eventually_residue_level_moment
--       (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
--       (hr : 0 ≤ r) :
--       ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
--         (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
--         (M : ℝ) ≤ Real.exp (DM * S) →
--         ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
--         ∀ t : ℕ, t ∣ M →
--         (∑ h ∈ Finset.Icc 1
--             ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
--           densityDivisorCount
--             (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
--             (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
--             ^ r) ≤
--           ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
--             Real.exp (S ^ (1 / 4 : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem337.densityDivisorCount`, `OAI.Problem337.ResidueLevels.depth`, `OAI.Problem337.ResidueLevels.factor`, `OAI.Problem337.ResidueLevels.level` and `OAI.Problem337.ResidueLevels.scale` (definitions bundle `OAIQ8EF000` of this split).
--
--   **Used by.** The proof of `OAI.Problem337.main_double_log_order` of this split imports it.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/DensityMomentBound.lean (declaration OAI.Problem337.eventually_residue_level_moment)

import Mathlib
import Definitions.Def_OAIQ8EF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

theorem eventually_residue_level_moment
    (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
      (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
      ∀ t : ℕ, t ∣ M →
      (∑ h ∈ Finset.Icc 1
          ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
        densityDivisorCount
          (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
          (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
          ^ r) ≤
        ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  sorry

end Problem337

end

end OAI
end
