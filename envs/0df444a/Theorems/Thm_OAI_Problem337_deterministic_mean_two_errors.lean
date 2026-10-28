-- Prove2me | Theorems.Thm_OAI_Problem337_deterministic_mean_two_errors
-- name    : OAI.Problem337.deterministic_mean_two_errors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:26.003192+00:00
-- url     : https://prove2.me/theorems/974fe2fd-a9d0-4c72-8815-ad774f5618fa
-- title:
--   OAI.Problem337.deterministic_mean_two_errors: intermediate lemma from OpenAI, Short Egyptian fractions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem337.deterministic_mean_two_errors` of [lean/OAI/NumberTheory/EgyptianFractions/DeterministicMean.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/DeterministicMean.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem337`, with `open scoped BigOperators`, `open Filter ComplexConjugate`):
--
--   ```lean
--   theorem deterministic_mean_two_errors (D : ℝ) (hD : 255 ≤ D) :
--       ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
--         ∀ᶠ S : ℝ in atTop, ∀ (m X C ell : ℝ),
--           m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
--           Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
--           1 ≤ ell → ell ≤ Real.exp (m / 2500) →
--           ∀ {β : Type*} (T : Finset β) (t : β → ℕ),
--             Set.InjOn t (T : Set β) →
--             Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
--             (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
--             (∑ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
--               ‖(∑ i ∈ T, differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))) /
--                 (T.card : ℂ)‖ ^ 2) ≤
--               X * (Real.exp (-Real.log 2 * m) + A * Real.exp (-c * S))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem337.differencingPhase` (definitions bundle `OAIQ8EF000` of this split).
--
--   **Used by.** The proof of `OAI.Problem337.main_double_log_order` of this split imports it.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/DeterministicMean.lean (declaration OAI.Problem337.deterministic_mean_two_errors)

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
open Filter ComplexConjugate
namespace Problem337

theorem deterministic_mean_two_errors (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m X C ell : ℝ),
        m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
        1 ≤ ell → ell ≤ Real.exp (m / 2500) →
        ∀ {β : Type*} (T : Finset β) (t : β → ℕ),
          Set.InjOn t (T : Set β) →
          Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
          (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
          (∑ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            ‖(∑ i ∈ T, differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))) /
              (T.card : ℂ)‖ ^ 2) ≤
            X * (Real.exp (-Real.log 2 * m) + A * Real.exp (-c * S)) := by
  sorry

end Problem337

end

end OAI
end
