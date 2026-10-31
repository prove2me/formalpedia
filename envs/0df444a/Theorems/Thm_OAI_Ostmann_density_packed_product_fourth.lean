-- Prove2me | Theorems.Thm_OAI_Ostmann_density_packed_product_fourth
-- name    : OAI.Ostmann.density_packed_product_fourth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:00:51.830116+00:00
-- url     : https://prove2.me/theorems/1742a4a5-4001-46ab-86b7-a34a52efdbf7
-- title:
--   OAI.Ostmann.density_packed_product_fourth: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.density_packed_product_fourth` of [lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPackedProduct.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPackedProduct.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open MeasureTheory`, `open scoped BigOperators Classical`):
--
--   ```lean
--    theorem density_packed_product_fourth :
--       ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
--         ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
--         (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
--         (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
--         (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
--           ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ *
--           ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖) ^ 4 ≤
--             C * S.card * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
--               (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveComplexCharacter` and `OAI.Ostmann.PrimitiveComplexCharacter.L` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.densityCubicWeight`, `OAI.Ostmann.densityMollifier` and `OAI.Ostmann.densityVerticalPoint` (definitions bundle `OAIQ095D002` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.publishedComplexZeroDensity` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPackedProduct.lean (declaration OAI.Ostmann.density_packed_product_fourth)

import Mathlib
import Definitions.Def_OAIQ095D000
import Definitions.Def_OAIQ095D002

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_packed_product_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖) ^ 4 ≤
          C * S.card * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
            (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2 := by
  sorry

end Ostmann

end OAI
end
