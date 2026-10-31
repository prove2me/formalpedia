-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_character_anchor_decay
-- name    : OAI.Ostmann.eventual_character_anchor_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:08:18.091931+00:00
-- url     : https://prove2.me/theorems/3eb10262-63a0-4435-90db-64fc363766a5
-- title:
--   OAI.Ostmann.eventual_character_anchor_decay: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_character_anchor_decay` of [lean/OAI/NumberTheory/Ostmann/Characters/CharacterAnchorDecay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterAnchorDecay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem eventual_character_anchor_decay (k n Bnb : ℕ) (hn : n < k)
--       (ψ : 𝓢(ℝ, ℂ)) (K B B₁ z c a b Cmass α β ε : ℝ)
--       (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
--       (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
--       (hα : 0 < α) (hβ : 0 ≤ β) (hε : 0 < ε)
--       (hbudget : 4 * Cmass * Bnb ≤ z)
--       (hgap : 2 * B₁ +
--         ((β + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
--         Real.log 2 + 6 ≤ B + 20 * Real.log a)
--       (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
--       ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
--         (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
--         ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
--         1 + ((∑ j, r j) + 2 * k) ≤ Bnb →
--         ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
--           (Q : Fin (m + 1) → Finset ℕ)
--           (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
--         (∀ i : Fin m, Q i.succ = U) →
--         (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
--         b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
--         (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
--         (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
--         (∀ p ∈ U, (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
--         ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
--         let Δ := characterBaseGap B z m
--         let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
--           (fun j => characterPivotGap B z m j.val)
--         ∀ lower upper : CharacterCell k → ℕ,
--         (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
--         (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
--         ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p),
--         let lo := initialWordAtomLower J lower
--         let hi := initialWordAtomUpper J upper
--         let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
--         let Q₀ := characterFullPrimeCells m r f Q R
--         let V := naturalTransferCutoff Δ m
--         let cap := characterPivotCap T (characterRangeError k c)
--         let p := characterPivotAtom ⟨n, hn⟩
--         (∑ N ∈ Finset.Icc (lo p) (hi p),
--           (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
--             (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) n P hP Q₀
--             V cap (atomIntervalRanges (characterRole k) lo hi)
--             (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
--               (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
--               (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
--             (scheduledFrequencyHistory V n)
--             (selectedAnchorMatchingSet
--               (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
--               n m (characterBulk m r f) (characterBulk_role m r f)) N).re) ≤
--           Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * (m : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CharacterCell`, `OAI.Ostmann.CharacterRole`, `OAI.Ostmann.ScheduledFrequencyIndex` and `OAI.Ostmann.scheduledFrequencyHistory` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.characterBaseGap`, `OAI.Ostmann.characterPivotCap`, `OAI.Ostmann.characterPivotGap`, `OAI.Ostmann.characterPivotTarget`, `OAI.Ostmann.characterRangeError`, `OAI.Ostmann.initialWordAtomLower`, `OAI.Ostmann.initialWordAtomUpper`, `OAI.Ostmann.initialWordSize`, `OAI.Ostmann.naturalTransferCutoff`, `OAI.Ostmann.primeGaussMultiplier` and `OAI.Ostmann.signedAtomCharacter` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.atomIntervalRanges`, `OAI.Ostmann.characterBulk`, `OAI.Ostmann.characterBulk_role`, `OAI.Ostmann.characterCellSize`, `OAI.Ostmann.characterFullPrimeCells`, `OAI.Ostmann.characterLogCenter`, `OAI.Ostmann.characterPivot`, `OAI.Ostmann.characterPivotAtom`, `OAI.Ostmann.characterRole`, `OAI.Ostmann.characterSize`, `OAI.Ostmann.constituentMatchingFamily`, `OAI.Ostmann.scheduleFourierLeaf`, `OAI.Ostmann.scheduledFrequencyIndexFintype` and `OAI.Ostmann.selectedAnchorMatchingSet` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterAnchorDecay.lean (declaration OAI.Ostmann.eventual_character_anchor_decay)

import Mathlib
import Definitions.Def_OAIQ095D004

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_character_anchor_decay (k n Bnb : ℕ) (hn : n < k)
    (ψ : 𝓢(ℝ, ℂ)) (K B B₁ z c a b Cmass α β ε : ℝ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((β + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * k) ≤ Bnb →
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
      (∀ p ∈ U, (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p),
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let Q₀ := characterFullPrimeCells m r f Q R
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      let p := characterPivotAtom ⟨n, hn⟩
      (∑ N ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi)
          (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet
            (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
            n m (characterBulk m r f) (characterBulk_role m r f)) N).re) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * (m : ℝ)) := by
  sorry

end Ostmann

end OAI
end
