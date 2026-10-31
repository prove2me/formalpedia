-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_character_final_contradiction
-- name    : OAI.Ostmann.eventual_character_final_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:22:00.819124+00:00
-- url     : https://prove2.me/theorems/0616b32f-39cc-4389-bf2c-5bcd2edb6449
-- title:
--   OAI.Ostmann.eventual_character_final_contradiction: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_character_final_contradiction` of [lean/OAI/NumberTheory/Ostmann/Characters/CharacterFinalContradiction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterFinalContradiction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate`):
--
--   ```lean
--   theorem eventual_character_final_contradiction (n N : ℕ)
--       (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
--       (K B B₁ z c Cmass α βg βw γs νw ε : ℝ)
--       (hB : 1 ≤ B) (hB₁ : 0 ≤ B₁) (hz : 1 ≤ z) (hc : 1 ≤ c)
--       (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg)
--       (hαw : α < βw) (hsw : γs < βw) (hβw : βw < νw) (hε : 0 < ε)
--       (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
--       (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
--         (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
--       ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
--         L ≤ m → (m : ℝ) ≤ z * L →
--         ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
--         (∀ j, r j ≤ N) → f ≤ N →
--         ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
--           (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
--         (∀ i, Q i ⊆ P) →
--         (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
--         (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
--           (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
--         (∀ j p, p ∈ Q (characterAnchor m r f j false) →
--           (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
--         (∀ i p, p ∈ Q (characterBulk m r f i) → Real.exp (Real.exp (νw * L)) ≤ p) →
--         (∀ i : Fin m, 1 ≤ ∑ p ∈ Q (characterBulk m r f i), (p : ℝ)⁻¹) →
--         ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
--         ∀ (J : ℕ) (lower upper : CharacterCell (n + 1) → ℕ) (logX : ℝ), 0 < logX →
--         let Δ := characterBaseGap B z m
--         let lo := initialWordAtomLower J lower
--         let hi := initialWordAtomUpper J upper
--         let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
--         let V := naturalTransferCutoff Δ m
--         ∀ (cap : ℕ → ℕ) (center : ∀ p : ℕ, ZMod p),
--         Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤
--           ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
--             (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP Q lo hi V cap
--             (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
--               (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
--               (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center (n + 1)‖ →
--         False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CharacterCell` and `OAI.Ostmann.CharacterRole` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.characterBaseGap`, `OAI.Ostmann.initialWordAtomLower`, `OAI.Ostmann.initialWordAtomUpper`, `OAI.Ostmann.initialWordSize`, `OAI.Ostmann.naturalTransferCutoff`, `OAI.Ostmann.primeGaussMultiplier` and `OAI.Ostmann.signedAtomCharacter` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.characterAnchor`, `OAI.Ostmann.characterBulk`, `OAI.Ostmann.characterCellSize`, `OAI.Ostmann.characterPivot`, `OAI.Ostmann.characterRole`, `OAI.Ostmann.characterSize` and `OAI.Ostmann.scheduleFourierLeaf` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.scheduledConstituentAmplitude` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterFinalContradiction.lean (declaration OAI.Ostmann.eventual_character_final_contradiction)

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
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_final_contradiction (n N : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c Cmass α βg βw γs νw ε : ℝ)
    (hB : 1 ≤ B) (hB₁ : 0 ≤ B₁) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg)
    (hαw : α < βw) (hsw : γs < βw) (hβw : βw < νw) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
      L ≤ m → (m : ℝ) ≤ z * L →
      ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
      (∀ i, Q i ⊆ P) →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j false) →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ i p, p ∈ Q (characterBulk m r f i) → Real.exp (Real.exp (νw * L)) ≤ p) →
      (∀ i : Fin m, 1 ≤ ∑ p ∈ Q (characterBulk m r f i), (p : ℝ)⁻¹) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ) (lower upper : CharacterCell (n + 1) → ℕ) (logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      ∀ (cap : ℕ → ℕ) (center : ∀ p : ℕ, ZMod p),
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP Q lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center (n + 1)‖ →
      False := by
  sorry

end Ostmann

end OAI
end
