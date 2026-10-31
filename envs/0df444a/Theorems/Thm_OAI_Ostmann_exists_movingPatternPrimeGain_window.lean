-- Prove2me | Theorems.Thm_OAI_Ostmann_exists_movingPatternPrimeGain_window
-- name    : OAI.Ostmann.exists_movingPatternPrimeGain_window
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:25:00.297521+00:00
-- url     : https://prove2.me/theorems/2fa86856-b4d5-4616-8989-e31656f872e2
-- title:
--   OAI.Ostmann.exists_movingPatternPrimeGain_window: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.exists_movingPatternPrimeGain_window` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternWindowPrimeGain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternWindowPrimeGain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem exists_movingPatternPrimeGain_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
--       (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
--       ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
--         ∀ (m : ℕ), 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
--         hi - lo ≤ Real.exp (H * m) → ∀ (Bidx Cidx : Type) (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (base : Fin (N + 1) → ℕ)
--           (t : Bool → FrequencyTree ℤ (n + 2))
--           (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
--           (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime],
--         (∀ i, cutoff ≤ p i) →
--         (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0 ∧ s.natAbs < p i) →
--         (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
--           (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
--         (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
--         ∀ (twist : ∀ i, Bool → (ZMod (p i))ˣ)
--           (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
--         4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
--           3 * Fintype.card (TreeLeafIndex (n + 2)) →
--         ∀ S : ∀ i, Finset (ZMod (p i)),
--         (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
--         (∀ i, residueDensity (S i) ≤ 2 / 3) →
--         (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
--         ∀ β : Fin m → ℝ, (∀ i, 2 * β i ≤ ε) →
--         (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
--           ‖((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, χ⁻¹ (-a - x)‖ ≤ β i) →
--         ∀ amp : ℝ, 0 ≤ amp → amp ≤ Real.exp (F * m) →
--         let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
--           (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
--         (∀ i, ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
--             ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
--               (fun b => movingPatternFiniteSmall e (n + 2) (small b))
--               (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
--               (normalizedResidueTransform (S i)) z‖ ≤ δ) ∧
--           (W * amp) * 4 ^ Fintype.card (TreeLeafIndex (n + 2) × Fin m) *
--             δ ^ m ≤ Real.exp (-gain * m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.arrangementGraph`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.instFintypeConnectedComponentSumArrangementGraph`, `OAI.Ostmann.residueDensity` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.movingFourierVariationBudget` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.frozenBulkSpectatorHaar`, `OAI.Ostmann.normalizedResidueTransform` and `OAI.Ostmann.treeLeafIndexDecidableEq` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternFiniteSmall` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.movingPatternFiniteSamples` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_selected_prime_rate_window` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternWindowPrimeGain.lean (declaration OAI.Ostmann.exists_movingPatternPrimeGain_window)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem exists_movingPatternPrimeGain_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) → ∀ (Bidx Cidx : Type) (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (base : Fin (N + 1) → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime],
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0 ∧ s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
      ∀ (twist : ∀ i, Bool → (ZMod (p i))ˣ)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ S : ∀ i, Finset (ZMod (p i)),
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
      (∀ i, residueDensity (S i) ≤ 2 / 3) →
      (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
      ∀ β : Fin m → ℝ, (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, χ⁻¹ (-a - x)‖ ≤ β i) →
      ∀ amp : ℝ, 0 ≤ amp → amp ≤ Real.exp (F * m) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ i, ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
          ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
            (fun b => movingPatternFiniteSmall e (n + 2) (small b))
            (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
            (normalizedResidueTransform (S i)) z‖ ≤ δ) ∧
        (W * amp) * 4 ^ Fintype.card (TreeLeafIndex (n + 2) × Fin m) *
          δ ^ m ≤ Real.exp (-gain * m) := by
  sorry

end Ostmann

end OAI
end
