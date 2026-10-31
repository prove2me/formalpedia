-- Prove2me | Theorems.Thm_OAI_Ostmann_common_center_biased_populations_impossible
-- name    : OAI.Ostmann.common_center_biased_populations_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:04:43.406503+00:00
-- url     : https://prove2.me/theorems/630bf0d0-18e6-4dcc-9a00-20c3e0e6699c
-- title:
--   OAI.Ostmann.common_center_biased_populations_impossible: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.common_center_biased_populations_impossible` of [lean/OAI/NumberTheory/Ostmann/Quadratic/CommonCenterPopulationContradiction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/CommonCenterPopulationContradiction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem common_center_biased_populations_impossible (P₀ : PublishedProgressionInput)
--       (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve)
--       (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
--       (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
--       ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
--         ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
--           (h : ℤ) (ε δ : ℕ → ℝ) (t : ℕ → ℤ) (S U : Finset ℤ),
--           T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
--           2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
--           0 < J → Real.exp T ≤ Cpop * T * J →
--           J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
--           Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
--           1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
--           ∀ hP : ∀ p ∈ P, p.Prime,
--           (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
--           (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
--           (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → (∀ p ∈ P, m < p) →
--           (∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
--             (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) →
--           0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
--           (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) → (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
--           (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) →
--           (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ x ∈ U, orientedQuadraticValue δ t x p) →
--           (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
--           (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
--           (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
--             kernelSplitCutoff η L < (x - y).natAbs) →
--           a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
--           a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensLowerBound` and `OAI.Ostmann.PublishedQuadraticLargeSieve` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.kernelSplitCutoff` and `OAI.Ostmann.orientedQuadraticValue` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput` and `OAI.Ostmann.PublishedSiegelBound` (definitions bundle `OAIQ095D003` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.quadraticBandMass_isLittleO` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Quadratic/CommonCenterPopulationContradiction.lean (declaration OAI.Ostmann.common_center_biased_populations_impossible)

import Mathlib
import Definitions.Def_OAIQ095D002
import Definitions.Def_OAIQ095D003

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem common_center_biased_populations_impossible (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
        (h : ℤ) (ε δ : ℕ → ℝ) (t : ℕ → ℤ) (S U : Finset ℤ),
        T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
        2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
        0 < J → Real.exp T ≤ Cpop * T * J →
        J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
        Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
        1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
        ∀ hP : ∀ p ∈ P, p.Prime,
        (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
        (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
        (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → (∀ p ∈ P, m < p) →
        (∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) →
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) → (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
        (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) →
        (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ x ∈ U, orientedQuadraticValue δ t x p) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False := by
  sorry

end Ostmann

end OAI
end
