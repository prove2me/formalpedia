-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_character_atom_iteration
-- name    : OAI.Ostmann.eventual_character_atom_iteration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:50.660968+00:00
-- url     : https://prove2.me/theorems/88e2f766-6f54-4e4f-96f7-b2d8e95e5cd3
-- title:
--   OAI.Ostmann.eventual_character_atom_iteration: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_character_atom_iteration` of [lean/OAI/NumberTheory/Ostmann/Characters/CharacterAtomIteration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterAtomIteration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem eventual_character_atom_iteration (k : ℕ) (r : Fin k → ℕ) (f : ℕ)
--       (hr : ∀ j, 0 < r j) (B B₀ z c Cmass : ℝ)
--       (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 ≤ Cmass)
--       (hbudget : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4) :
--       ∀ᶠ L : ℝ in atTop,
--       let m := ⌊z * L⌋₊
--       ∀ (J : ℕ), 0 < J → ∀ (a : Fin k → Bool → ℝ) (F : ℝ),
--       let T := characterPivotTarget k J (fun j => a j false + a j true)
--         (fun j => characterPivotGap B z m j.val)
--       let V := naturalTransferCutoff (characterBaseGap B z m) m
--       let cap := characterPivotCap T (characterRangeError k c)
--       ∀ (cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ),
--       let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
--       let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
--       ∀ (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
--         (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
--         (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
--         (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ)
--         (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p),
--       (∀ i q, q ∈ P → ‖κ i q‖ ≤ 1) →
--       (∀ i, Q i ⊆ P) → (∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0) →
--       (∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i) →
--       (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤
--         ∏ i, cellLo ⟨(true, some v), i⟩) →
--       (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
--         Real.exp (characterLogCenter J T a F (true, some v) + c)) →
--       (∀ j : Fin k, ∀ i : Fin (r j),
--         (∑ q ∈ Q ⟨characterPivotAtom j, i⟩, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (Cmass * L)) →
--       (∀ q ∈ P, V k < q) →
--       (Real.exp (-B₀ * m) ≤ ‖scheduledConstituentAmplitude (characterRole k)
--         (characterSize m r f) χ κ (characterPivot m r f hr) P hP Q lo hi V cap leaf center 0‖) →
--       (∀ j < k, scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ
--         (characterPivot m r f hr) P hP Q lo hi V cap leaf center (characterPivotRole k j) j ≤
--           Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) →
--       Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
--         ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ κ
--           (characterPivot m r f hr) P hP Q lo hi V cap leaf center k‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CharacterCell`, `OAI.Ostmann.CharacterRole` and `OAI.Ostmann.ScheduleAtomState` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.characterBaseGap`, `OAI.Ostmann.characterPivotCap`, `OAI.Ostmann.characterPivotGap`, `OAI.Ostmann.characterPivotTarget`, `OAI.Ostmann.characterRangeError`, `OAI.Ostmann.initialWordAtomLower`, `OAI.Ostmann.initialWordAtomUpper` and `OAI.Ostmann.naturalTransferCutoff` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.characterLogCenter`, `OAI.Ostmann.characterPivot`, `OAI.Ostmann.characterPivotAtom`, `OAI.Ostmann.characterPivotRole`, `OAI.Ostmann.characterRole` and `OAI.Ostmann.characterSize` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.scheduledConstituentAmplitude` and `OAI.Ostmann.scheduledConstituentDiagonal` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterAtomIteration.lean (declaration OAI.Ostmann.eventual_character_atom_iteration)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_atom_iteration (k : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (B B₀ z c Cmass : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 ≤ Cmass)
    (hbudget : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (J : ℕ), 0 < J → ∀ (a : Fin k → Bool → ℝ) (F : ℝ),
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let V := naturalTransferCutoff (characterBaseGap B z m) m
    let cap := characterPivotCap T (characterRangeError k c)
    ∀ (cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ),
    let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
    ∀ (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
      (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ)
      (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p),
    (∀ i q, q ∈ P → ‖κ i q‖ ≤ 1) →
    (∀ i, Q i ⊆ P) → (∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0) →
    (∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i) →
    (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤
      ∏ i, cellLo ⟨(true, some v), i⟩) →
    (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
      Real.exp (characterLogCenter J T a F (true, some v) + c)) →
    (∀ j : Fin k, ∀ i : Fin (r j),
      (∑ q ∈ Q ⟨characterPivotAtom j, i⟩, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (Cmass * L)) →
    (∀ q ∈ P, V k < q) →
    (Real.exp (-B₀ * m) ≤ ‖scheduledConstituentAmplitude (characterRole k)
      (characterSize m r f) χ κ (characterPivot m r f hr) P hP Q lo hi V cap leaf center 0‖) →
    (∀ j < k, scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ
      (characterPivot m r f hr) P hP Q lo hi V cap leaf center (characterPivotRole k j) j ≤
        Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) →
    Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
      ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ κ
        (characterPivot m r f hr) P hP Q lo hi V cap leaf center k‖ := by
  sorry

end Ostmann

end OAI
end
