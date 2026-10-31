-- Prove2me | Theorems.Thm_OAI_Ostmann_exists_selected_small_primes
-- name    : OAI.Ostmann.exists_selected_small_primes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:18.655958+00:00
-- url     : https://prove2.me/theorems/8e3c00c6-fb35-45af-8ac0-ecce16b7a1a7
-- title:
--   OAI.Ostmann.exists_selected_small_primes: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.exists_selected_small_primes` of [lean/OAI/NumberTheory/Ostmann/Construction/SelectedSmallPrimes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedSmallPrimes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem exists_selected_small_primes (hsize : PublishedSummandSizeBound)
--       {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
--       (C : ℝ) (hM : MertensEstimate C) :
--       ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
--         L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
--         ∀ hi : ℕ, (hi : ℝ) = Real.exp L → ∀ V : ℝ, T / 2 ≤ V → V ≤ 2 * T →
--         ∃ Q : Finset ℕ,
--           (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p ∧ Real.log (p : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) ∧
--           3000 ≤ Q.card ∧ V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) ∧
--           (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) ∧
--           2 ≤ Q.toList.prod ∧ (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) ∧
--           (∀ p ∈ Q, (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3) ∧
--           (∀ n ∈ positiveSummandTail A (summandTailCutoff L) hi,
--             ∀ p ∈ Q, (n : ZMod p) ∈ tailDensityMask A N p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.positiveSummandTail`, `OAI.Ostmann.summandTailCutoff` and `OAI.Ostmann.tailDensityMask` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.quadraticBandMass_isLittleO` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedSmallPrimes.lean (declaration OAI.Ostmann.exists_selected_small_primes)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_selected_small_primes (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
      L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L → ∀ V : ℝ, T / 2 ≤ V → V ≤ 2 * T →
      ∃ Q : Finset ℕ,
        (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p ∧ Real.log (p : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) ∧
        3000 ≤ Q.card ∧ V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) ∧
        (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) ∧
        2 ≤ Q.toList.prod ∧ (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) ∧
        (∀ p ∈ Q, (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3) ∧
        (∀ n ∈ positiveSummandTail A (summandTailCutoff L) hi,
          ∀ p ∈ Q, (n : ZMod p) ∈ tailDensityMask A N p) := by
  sorry

end Ostmann

end OAI
end
