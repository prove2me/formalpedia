-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_eventual_tested_character_shell_contradiction
-- name    : OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:05:33.763226+00:00
-- url     : https://prove2.me/theorems/43f2192d-b96a-4e34-ab00-2db3c76dc5aa
-- title:
--   OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction` of [lean/OAI/NumberTheory/Ostmann/Characters/CharacterTestedShellContradiction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterTestedShellContradiction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate`):
--
--   ```lean
--   theorem PublishedProgressionInput.eventual_tested_character_shell_contradiction
--       (P0 : PublishedProgressionInput) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
--       ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 20000 ≤ n + 1 →
--         C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
--       ∀
--       (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε β Ccode A : ℝ)
--       (_ha : 0 < a) (_hb : 0 < b) (_hz : 1 < z)
--       (_hCmass : 0 < Cmass) (_hCtotal : 0 ≤ Ctotal) (_hc : 1 ≤ c)
--       (_hs : 0 < s) (_hγ : 0 < γ) (_hH : 0 ≤ H) (_hα : 0 < α)
--       (_hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
--         (Aend + 2 * Bword + 1) + 2) ≤ B) (_hB : 0 ≤ B)
--       (_hB₁ : 0 ≤ B₁) (_hB₁eq : B₁ = Aend + 2 * Bword + 3)
--       (_hBstrong : 2 * B₁ + 5 ≤ B) (_hBpos : 1 ≤ B) (_ha1 : a ≤ 1)
--       (_hβg : 0 < βg) (_hγw : 0 ≤ γw) (_hαw : α < βw) (_hsw : γs < βw)
--       (_hαa : α < βa) (_hwa : γw < βa) (_hwg : γw ≤ βg)
--       (_hβw : βw < νw) (_hβa : βa < νa) (_hε : 0 < ε)
--       (_hbudgetAll : 4 * Cmass *
--         (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
--       (_hgapFinal : 2 * B₁ +
--         ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
--         Real.log 2 + 6 ≤ B + 20 * Real.log a)
--       (_hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
--         (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
--       (_hβ : 0 ≤ β) (_hβgap : β < βg)
--       (_hβmass : β + 1 ≤ Cmass)
--       (_hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
--       (_hCcode : 0 ≤ Ccode) (_hArate : A + (β + 1) + 4 * Ccode + 4 ≤ Aend)
--       (_hBrate : (β + 1) - 2 * Real.log δ ≤ Bword) (_hγδ : γ ≤ δ / 2)
--       (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
--       (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
--       (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
--       (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0),
--       ∀ᶠ L : ℝ in atTop,
--       let m := ⌊z * L⌋₊
--       ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
--         (Q : Fin (m + 1) → Finset ℕ) (D : ℕ),
--       α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
--       Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
--       Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
--       a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
--       (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
--       (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
--         (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
--       (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
--         (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
--       Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
--       (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
--       (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
--       ∀ (l h : ℝ),
--       (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
--       h ≤ Ulate →
--       (D + 1 : ℕ) ≤ Real.exp (Ccode * L) → 5 * (n + 1) ≤ D →
--       (∀ p ∈ P, primeLogIndex p ≤ D) →
--       (∀ u v : ℝ, Ulate ≤ u → v ≤ Ulate + 5 * (n + 1) →
--         ((n + 1 : ℕ) : ℝ) / 10000 ≤ v - u →
--         ∃ j : ℕ, u ≤ Ulate + j ∧ Ulate + j + 1 ≤ v ∧
--           c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) →
--       ∀ u : Fin (n + 1) × Bool → ℝ,
--       (∀ j, α * L ≤ u j ∧ u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
--       (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
--       (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
--       (∀ j, c₀ ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
--       ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
--       ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
--       ∀ E : Finset ℕ,
--       Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
--         Real.exp (-A * m) ≤ E.card →
--       (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
--       (∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) *
--         χ p ((x : ZMod p) - center p)‖) →
--       (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * (n + 1) →
--         c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
--         (∀ p ∈ loglogShell P (Ulate + j),
--           Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ (n + 1) * τ) / 4) →
--         δ * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
--           ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
--             (ζ * χ p ((x : ZMod p) - center p)).re) →
--       (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
--         ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) →
--       False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.loglogShell`, `OAI.Ostmann.primeLogIndex` and `OAI.Ostmann.primeSubsetPrior` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.characterCellCoveringError` and `OAI.Ostmann.characterTargetLabelBound` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/CharacterTestedShellContradiction.lean (declaration OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction)

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
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.eventual_tested_character_shell_contradiction
    (P0 : PublishedProgressionInput) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
    ∀
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε β Ccode A : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hz : 1 < z)
    (_hCmass : 0 < Cmass) (_hCtotal : 0 ≤ Ctotal) (_hc : 1 ≤ c)
    (_hs : 0 < s) (_hγ : 0 < γ) (_hH : 0 ≤ H) (_hα : 0 < α)
    (_hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (_hB : 0 ≤ B)
    (_hB₁ : 0 ≤ B₁) (_hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (_hBstrong : 2 * B₁ + 5 ≤ B) (_hBpos : 1 ≤ B) (_ha1 : a ≤ 1)
    (_hβg : 0 < βg) (_hγw : 0 ≤ γw) (_hαw : α < βw) (_hsw : γs < βw)
    (_hαa : α < βa) (_hwa : γw < βa) (_hwg : γw ≤ βg)
    (_hβw : βw < νw) (_hβa : βa < νa) (_hε : 0 < ε)
    (_hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (_hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (_hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (_hβ : 0 ≤ β) (_hβgap : β < βg)
    (_hβmass : β + 1 ≤ Cmass)
    (_hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (_hCcode : 0 ≤ Ccode) (_hArate : A + (β + 1) + 4 * Ccode + 4 ≤ Aend)
    (_hBrate : (β + 1) - 2 * Real.log δ ≤ Bword) (_hγδ : γ ≤ δ / 2)
    (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
    (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0),
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (D : ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (l h : ℝ),
    (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
    h ≤ Ulate →
    (D + 1 : ℕ) ≤ Real.exp (Ccode * L) → 5 * (n + 1) ≤ D →
    (∀ p ∈ P, primeLogIndex p ≤ D) →
    (∀ u v : ℝ, Ulate ≤ u → v ≤ Ulate + 5 * (n + 1) →
      ((n + 1 : ℕ) : ℝ) / 10000 ≤ v - u →
      ∃ j : ℕ, u ≤ Ulate + j ∧ Ulate + j + 1 ≤ v ∧
        c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) →
    ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, α * L ≤ u j ∧ u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    (∀ j, c₀ ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
    ∀ E : Finset ℕ,
    Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
      Real.exp (-A * m) ≤ E.card →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
    (∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) *
      χ p ((x : ZMod p) - center p)‖) →
    (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * (n + 1) →
      c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
      (∀ p ∈ loglogShell P (Ulate + j),
        Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ (n + 1) * τ) / 4) →
      δ * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
          (ζ * χ p ((x : ZMod p) - center p)).re) →
    (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
      ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) →
    False := by
  sorry

end Ostmann

end OAI
end
