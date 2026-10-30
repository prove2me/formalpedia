-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_original_tail_commonCenter
-- name    : OAI.Ostmann.eventual_original_tail_commonCenter
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:10.141143+00:00
-- url     : https://prove2.me/theorems/ff86eead-8981-4327-99d1-2248ae45b579
-- title:
--   OAI.Ostmann.eventual_original_tail_commonCenter: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_original_tail_commonCenter` of [lean/OAI/NumberTheory/Ostmann/Construction/OriginalTailCenter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalTailCenter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical`):
--
--   ```lean
--   theorem eventual_original_tail_commonCenter (hBonami : PublishedBonamiBound)
--       (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
--       (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
--       (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
--       (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
--       (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
--       ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
--         ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
--         ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
--         1 ≤ X → B ^ 2 < X / Q.toList.prod →
--         ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
--         a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
--         (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
--         (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
--         ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
--         (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
--         ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
--         T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
--         T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
--         3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
--         (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
--         2 ≤ Q.toList.prod →
--         Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
--         X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
--         (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
--         (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
--         1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
--         1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
--         1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
--         (∀ M ∈ primeSubsetProducts P k,
--           B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
--           Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
--         ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
--           ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
--             (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
--             0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
--             Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
--             (P.card : ℝ) * Real.exp (-T / (k - 1 : ℕ)) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
--             ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
--               let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
--               (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PublishedBonamiBound` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.matchingPrimes`, `OAI.Ostmann.orientedQuadraticValue` and `OAI.Ostmann.primeSubsetProducts` (definitions bundle `OAIQ095D002` of this split).
--
--   **Used by.** The proofs of `OAI_Ostmann_eventual_dyadic_two_tail_contradiction` and `OAI.Ostmann.quadraticBandMass_isLittleO` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalTailCenter.lean (declaration OAI.Ostmann.eventual_original_tail_commonCenter)

import Mathlib
import Definitions.Def_OAIQ095D001
import Definitions.Def_OAIQ095D002

section

attribute [-instance] _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_original_tail_commonCenter (hBonami : PublishedBonamiBound)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (X : ℝ),
      1 ≤ X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
        ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
          (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
          0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
          Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          (P.card : ℝ) * Real.exp (-T / (k - 1 : ℕ)) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
            let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
            (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  sorry

end Ostmann

end OAI
end
