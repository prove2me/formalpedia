-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_original_witness_probability
-- name    : OAI.Ostmann.eventual_original_witness_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:27:30.155547+00:00
-- url     : https://prove2.me/theorems/ee38e210-8bf0-4cf4-a28f-e96010253df1
-- title:
--   OAI.Ostmann.eventual_original_witness_probability: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_original_witness_probability` of [lean/OAI/NumberTheory/Ostmann/Construction/OriginalWitnessProbability.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalWitnessProbability.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators SchwartzMap Classical`):
--
--   ```lean
--   theorem eventual_original_witness_probability (hB : PublishedBonamiBound)
--       (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
--       (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
--       (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
--       ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
--         (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
--         T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
--         3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
--         (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
--         2 ≤ Q.toList.prod →
--         (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
--         (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
--         1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
--         1 ≤ k → 2 * k ^ 2 ≤ P.card →
--         T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
--         1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
--         1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
--         ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
--         (∀ m ∈ primeSubsetProducts P k,
--           h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
--           R m ≤ Real.exp (14 * T) ∧
--           (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
--         (∀ m ∈ primeSubsetProducts P k, H * R m * Q.toList.prod ≤ N) →
--         Real.exp ((3 / 200 : ℝ) * Q.card) ≤ (P.card.choose k : ℝ)⁻¹ *
--           (∑ m ∈ primeSubsetProducts P k,
--             ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) →
--         Real.exp (-(Q.card : ℝ) / 5) ≤ (P.card.choose k : ℝ)⁻¹ *
--           ((primeSubsetProducts P k).filter (fun m =>
--             principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PublishedBonamiBound` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.primeSubsetProducts` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.originalPositiveFourier` and `OAI.Ostmann.principalSmallWitness` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_original_tail_commonCenter` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalWitnessProbability.lean (declaration OAI.Ostmann.eventual_original_witness_probability)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem eventual_original_witness_probability (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      2 ≤ Q.toList.prod →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (∀ m ∈ primeSubsetProducts P k, H * R m * Q.toList.prod ≤ N) →
      Real.exp ((3 / 200 : ℝ) * Q.card) ≤ (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) →
      Real.exp (-(Q.card : ℝ) / 5) ≤ (P.card.choose k : ℝ)⁻¹ *
        ((primeSubsetProducts P k).filter (fun m =>
          principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)).card := by
  sorry

end Ostmann

end OAI
end
