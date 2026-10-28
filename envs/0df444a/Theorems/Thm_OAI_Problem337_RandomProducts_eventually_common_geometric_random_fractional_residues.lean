-- Prove2me | Theorems.Thm_OAI_Problem337_RandomProducts_eventually_common_geometric_random_fractional_residues
-- name    : OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:20.490869+00:00
-- url     : https://prove2.me/theorems/0c134771-5464-45b5-85f6-fc4b45feff05
-- title:
--   OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues: intermediate lemma from OpenAI, Short Egyptian fractions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues` of [lean/OAI/NumberTheory/EgyptianFractions/GeometricRandomResidues.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/GeometricRandomResidues.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem337.RandomProducts`, with `open Filter`, `open scoped BigOperators`, `open GeometricRandomRanges`):
--
--   ```lean
--   theorem eventually_common_geometric_random_fractional_residues (D : ℝ) (hD : 1 ≤ D) :
--       ∀ᶠ S : ℝ in atTop, ∀ P : Finset ℕ,
--         (∀ p ∈ P, Nat.Prime p) →
--         (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
--         S ^ 99 ≤ (P.card : ℝ) →
--         ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
--           (exceptional : ℕ → Finset ℕ),
--           (∀ j ∈ middleTests D S, exceptional j ⊆ middleLevel D S j ∧
--             ((exceptional j).card : ℝ) ≤
--               cutoff D S j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
--             ∀ u ∈ middleLevel D S j, u ∉ exceptional j →
--               (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
--                   (2 : ℝ) ^ blockLength S ≤
--                 ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
--                   Int.fract (-(sampledProduct (f 0) I : ℝ) / u) <
--                     Real.exp (-(blockLength S : ℝ) / 10000))).card : ℝ)) ∧
--           ∀ u ∈ terminalRange S, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
--             (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem337.GeometricRandomRanges.cutoff`, `OAI.Problem337.GeometricRandomRanges.middleLevel`, `OAI.Problem337.GeometricRandomRanges.middleTests`, `OAI.Problem337.GeometricRandomRanges.terminalRange`, `OAI.Problem337.RandomProducts.blockLength`, `OAI.Problem337.RandomProducts.sampledProduct` and `OAI.Problem337.RandomProducts.sampledRemainder` (definitions bundle `OAIQ8EF000` of this split).
--
--   **Used by.** The proof of `OAI.Problem337.main_double_log_order` of this split imports it.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/EgyptianFractions/GeometricRandomResidues.lean (declaration OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues)

import Mathlib
import Definitions.Def_OAIQ8EF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.RandomProducts
open GeometricRandomRanges

theorem eventually_common_geometric_random_fractional_residues (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : ℕ → Finset ℕ),
        (∀ j ∈ middleTests D S, exceptional j ⊆ middleLevel D S j ∧
          ((exceptional j).card : ℝ) ≤
            cutoff D S j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ middleLevel D S j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                Int.fract (-(sampledProduct (f 0) I : ℝ) / u) <
                  Real.exp (-(blockLength S : ℝ) / 10000))).card : ℝ)) ∧
        ∀ u ∈ terminalRange S, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  sorry

end Problem337.RandomProducts

end

end OAI
end
