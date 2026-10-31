-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_original_tuple_witness_lift
-- name    : OAI.Ostmann.eventual_original_tuple_witness_lift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:22:49.455113+00:00
-- url     : https://prove2.me/theorems/96a1db92-ae98-4091-8b74-2531996ec64e
-- title:
--   OAI.Ostmann.eventual_original_tuple_witness_lift: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_original_tuple_witness_lift` of [lean/OAI/NumberTheory/Ostmann/Construction/OriginalTupleLifts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalTupleLifts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators SchwartzMap Classical`):
--
--   ```lean
--   theorem eventual_original_tuple_witness_lift (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
--       (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
--       ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
--         (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
--         (k N : ℕ) (t τ : ℕ → ℤ) (h₀ : ℕ → ℕ) (X : ℝ),
--         0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
--         (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
--         (∀ m ∈ primeSubsetProducts P k,
--           Real.exp (10 * T) ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
--           ∀ p ∈ m.primeFactors, (p : ℤ) ∣ τ m - t p) →
--         ∀ e : Fin k ↪ P,
--           principalSmallWitness Q hQ D (primeTupleProduct P e) N (h₀ (primeTupleProduct P e))
--             ((τ (primeTupleProduct P e) : ℝ) / primeTupleProduct P e)
--             ((primeTupleProduct P e : ℝ) / X) Φ →
--           ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
--             ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
--               (⌈X * Real.exp (13 * T / 100)⌉₊ + 1),
--               ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.primeSubsetProducts` and `OAI.Ostmann.primeTupleProduct` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.principalSmallWitness` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_original_tail_commonCenter` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/OriginalTupleLifts.lean (declaration OAI.Ostmann.eventual_original_tuple_witness_lift)

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

theorem eventual_original_tuple_witness_lift (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (k N : ℕ) (t τ : ℕ → ℤ) (h₀ : ℕ → ℕ) (X : ℝ),
      0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ m ∈ primeSubsetProducts P k,
        Real.exp (10 * T) ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
        ∀ p ∈ m.primeFactors, (p : ℤ) ∣ τ m - t p) →
      ∀ e : Fin k ↪ P,
        principalSmallWitness Q hQ D (primeTupleProduct P e) N (h₀ (primeTupleProduct P e))
          ((τ (primeTupleProduct P e) : ℝ) / primeTupleProduct P e)
          ((primeTupleProduct P e : ℝ) / X) Φ →
        ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
          ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
            (⌈X * Real.exp (13 * T / 100)⌉₊ + 1),
            ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  sorry

end Ostmann

end OAI
end
