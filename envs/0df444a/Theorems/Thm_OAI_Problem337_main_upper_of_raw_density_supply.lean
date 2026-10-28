-- Prove2me | Theorems.Thm_OAI_Problem337_main_upper_of_raw_density_supply
-- name    : OAI.Problem337.main_upper_of_raw_density_supply
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:53.70332+00:00
-- url     : https://prove2.me/theorems/fd482cf2-26ae-432e-9456-c97f3bee9a37
-- title:
--   OAI.Problem337.main_upper_of_raw_density_supply: intermediate lemma from OpenAI, Short Egyptian fractions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem337.main_upper_of_raw_density_supply` of [lean/OAI/NumberTheory/EgyptianFractions/RawDensityUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/RawDensityUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem337`, with `open Filter`):
--
--   ```lean
--   theorem main_upper_of_raw_density_supply
--       (DM L c K r : ℝ) (hDM : 1 < DM) (hL : 0 < L)
--       (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
--       (hsupply : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
--         Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
--         (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
--         RawDensitySupply DM L c K r S C) :
--       ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
--         (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem337.RawDensitySupply` (definitions bundle `OAIQ8EF000` of this split); `OAI.Problem337.maxEgyptianLength` (the published bundle `Def_EgyptianFractions`).
--
--   **Used by.** The proof of `OAI.Problem337.main_double_log_order` of this split imports it.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/RawDensityUpper.lean (declaration OAI.Problem337.main_upper_of_raw_density_supply)

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

theorem main_upper_of_raw_density_supply
    (DM L c K r : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
    (hsupply : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      RawDensitySupply DM L c K r S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  sorry

end Problem337

end

end OAI
end
