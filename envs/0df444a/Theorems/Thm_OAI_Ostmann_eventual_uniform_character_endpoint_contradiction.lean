-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_uniform_character_endpoint_contradiction
-- name    : OAI.Ostmann.eventual_uniform_character_endpoint_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:53.369037+00:00
-- url     : https://prove2.me/theorems/f7b769f1-4316-4970-b8d1-9468507d50e4
-- title:
--   OAI.Ostmann.eventual_uniform_character_endpoint_contradiction: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction` of [lean/OAI/NumberTheory/Ostmann/Characters/CharacterUniformEndpoint.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterUniformEndpoint.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate`):
--
--   ```lean
--   theorem eventual_uniform_character_endpoint_contradiction (n N Bnb : ℕ)
--       (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
--       (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
--       (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
--       (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
--       (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
--         (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
--       (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
--       (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
--       (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
--       (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
--       (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
--       (hbudgetAll : 4 * Cmass * Bnb ≤ z)
--       (hgapFinal : 2 * B₁ +
--         ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
--         Real.log 2 + 6 ≤ B + 20 * Real.log a)
--       (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
--         (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
--       (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
--       (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
--       (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
--       (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
--       ∀ᶠ L : ℝ in atTop, ∀ nc : ℕ, nc ≤ Bnb →
--       let m := ⌊z * L⌋₊
--       ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
--       (∀ j, r j ≤ N) → f ≤ N →
--       1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
--       Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
--       ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
--         (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
--         (Q : Fin (m + 1) → Finset ℕ)
--         (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
--       0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
--       (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
--       a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
--       (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
--       (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
--       (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
--         (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
--       (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
--         (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
--       Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
--       (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
--         (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
--       (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
--         Real.exp (Real.exp (νa * L)) ≤ p) →
--       (m : ℝ) * bmax ≤ τ →
--       (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
--       (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
--       ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
--       (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
--       ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
--       let Δ := characterBaseGap B z m
--       let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
--         (fun j => characterPivotGap B z m j.val)
--       let F := characterFillerTarget logX Δ bin.val T anchor
--       (∀ j, T j + c ≤ Real.exp (βg * L)) →
--       (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
--         ∏ i, cellLo ⟨v, i⟩) →
--       (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
--         Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
--       ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
--       ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
--       Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
--       Real.exp (-Bword * m) ≤ ρ →
--       (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
--       (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
--         (fun _ p => χ p ((x : ZMod p) - center p))
--         (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
--       (∀ x ∈ E, ∀ v i, γ ≤
--         ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
--       False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CharacterCell` and `OAI.Ostmann.primeSubsetPrior` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.binnedWordAverage`, `OAI.Ostmann.characterBaseGap`, `OAI.Ostmann.characterFillerTarget`, `OAI.Ostmann.characterPivotGap`, `OAI.Ostmann.characterPivotTarget` and `OAI.Ostmann.wordLogBin` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.characterCellSize` and `OAI.Ostmann.characterLogCenter` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proofs of `OAI_Ostmann_PublishedProgressionInput_concrete_character_band_contradiction` and `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterUniformEndpoint.lean (declaration OAI.Ostmann.eventual_uniform_character_endpoint_contradiction)

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
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_uniform_character_endpoint_contradiction (n N Bnb : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass * Bnb ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ nc : ℕ, nc ≤ Bnb →
    let m := ⌊z * L⌋₊
    ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
    (∀ j, r j ≤ N) → f ≤ N →
    1 + ((∑ j, r j) + 2 * (n + 1)) ≤ Bnb →
    Cmass * (∑ j, (r j : ℝ)) ≤ z / 4 →
    ∀ (_cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (logX τ bmax : ℝ) (P U T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell (n + 1)) → Fin (characterCellSize r f v) → Finset ℕ),
    0 < logX → Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) →
    (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (∀ v i, Disjoint U (R v i)) →
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) →
    (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
    (∀ v i p, p ∈ R v i → cellLo ⟨v, i⟩ ≤ p ∧ p ≤ cellHi ⟨v, i⟩) →
    ∀ (anchor : Fin (n + 1) → Bool → ℝ) (bin : Fin (⌊4 * τ⌋₊ + 1)), 0 < bin.val →
    let Δ := characterBaseGap B z m
    let T := characterPivotTarget (n + 1) bin.val (fun j => anchor j false + anchor j true)
      (fun j => characterPivotGap B z m j.val)
    let F := characterFillerTarget logX Δ bin.val T anchor
    (∀ j, T j + c ≤ Real.exp (βg * L)) →
    (∀ v, Real.exp (characterLogCenter bin.val T anchor F (true, some v) - c) ≤
      ∏ i, cellLo ⟨v, i⟩) →
    (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤
      Real.exp (characterLogCenter bin.val T anchor F (true, some v) + c)) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ : ℝ),
    Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R v i) p : ℂ) * χ p ((x : ZMod p) - center p)‖) →
    False := by
  sorry

end Ostmann

end OAI
end
