-- Prove2me | Theorems.Thm_OAI_Ostmann_density_polynomial_alternative_balanced
-- name    : OAI.Ostmann.density_polynomial_alternative_balanced
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:06:30.590286+00:00
-- url     : https://prove2.me/theorems/22d628e6-efdc-4bcf-b1b0-27a7d52cc148
-- title:
--   OAI.Ostmann.density_polynomial_alternative_balanced: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.density_polynomial_alternative_balanced` of [lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPolynomialBalanced.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPolynomialBalanced.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped BigOperators Classical`):
--
--   ```lean
--    theorem density_polynomial_alternative_balanced :
--       ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
--         2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 → ∀ X : ℕ, 1 ≤ X → (Q : ℝ) ^ 2 * T ≤ X →
--         ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
--         (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
--         (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
--         (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
--         (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈
--           (Finset.Icc 1 ⌊((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ⌋₊).filter (fun n => X < n),
--           LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
--             densityDetectorWeight (n / (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ))‖) →
--         (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
--           (Real.log ((Q : ℝ) * T)) ^ 9
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.densityBalanceExponent`, `OAI.Ostmann.densityDetectorWeight`, `OAI.Ostmann.densityTargetExponent` and `OAI.Ostmann.densityVerticalPoint` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.densityDetectorCharacterCoefficient` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.publishedComplexZeroDensity` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/ZeroDensity/DensityPolynomialBalanced.lean (declaration OAI.Ostmann.density_polynomial_alternative_balanced)

import Mathlib
import Definitions.Def_OAIQ095D004

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators Classical

 theorem density_polynomial_alternative_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 → ∀ X : ℕ, 1 ≤ X → (Q : ℝ) ^ 2 * T ≤ X →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈
        (Finset.Icc 1 ⌊((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
          densityDetectorWeight (n / (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ))‖) →
      (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
  sorry

end Ostmann

end OAI
end
