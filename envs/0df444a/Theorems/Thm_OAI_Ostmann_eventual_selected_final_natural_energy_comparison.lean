-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_selected_final_natural_energy_comparison
-- name    : OAI.Ostmann.eventual_selected_final_natural_energy_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:18.363332+00:00
-- url     : https://prove2.me/theorems/32c4ce1e-23ef-44e4-b1d6-1f1f65cece44
-- title:
--   OAI.Ostmann.eventual_selected_final_natural_energy_comparison: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_selected_final_natural_energy_comparison` of [lean/OAI/NumberTheory/Ostmann/Construction/SelectedFinalNaturalEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedFinalNaturalEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem eventual_selected_final_natural_energy_comparison (n : ℕ)
--       (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
--       (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
--       ∀ᶠ M : ℝ in atTop,
--       let V := naturalTransferCutoff (d * M) M
--       ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
--         (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
--         (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
--         (pivot : ℕ → (Σ i, Fin (size i)))
--         (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
--         (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
--         (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
--         (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, role (bulk i).1 = .word)
--         (X lo upper : ℝ)
--         (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ V (n + 1) < p)
--         (cells : (Σ a, Fin (size a)) → Finset ℕ)
--         (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (d * M - C₀) ≤ lo)
--         (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
--         (h J : ℕ)
--         (_hsmall : V (n + 1) ^ ((2 ^ (n + 2) - 1) * (n + 3)) ≤ 2 ^ h)
--         (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
--         (a C₁ L : ℝ) (_ha : 0 < a) (_hL : 1 ≤ L)
--         (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
--         (center : ∀ p : ℕ, ZMod p) (E : ℝ) (_hE : 0 ≤ E)
--         (_hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
--           ∀ d d' : ScheduledFrequencyIndex V (n + 1), scheduledRootIndex V (n + 1) d = scheduledRootIndex V (n + 1) d' →
--           ‖∑ q : SurvivingConstituent role size (n + 1) → P,
--             ((∏ i, primeSubsetPrior P (cells (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
--             (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
--               childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
--               (scheduledFrequencyHistory V (n + 1) d) q *
--             conj (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
--               childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
--               (scheduledFrequencyHistory V (n + 1) d')
--               (fun i => q (selectedFinalRelativePerm (fun i : Σ a, Fin (size a) => role i.1) n m bulk hbulk e f i))))‖ ≤ E),
--         ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P
--           (fun p hp => (hP p hp).1) cells childBound pivotBound ranges
--           (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V (n + 1)) center‖ ^ 2 ≤
--         ((transferFrequencyRange (V (n + 1))).card : ℝ) *
--           (Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M) /
--             (Fintype.card (FinalParityReassignments n m) : ℝ) +
--           (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 * E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CopyScheduleAtoms`, `OAI.Ostmann.CopyScheduleRole`, `OAI.Ostmann.CopyScheduleSurvives`, `OAI.Ostmann.CopyScheduleVertex`, `OAI.Ostmann.FinalParityReassignments`, `OAI.Ostmann.ScheduleAtomRange`, `OAI.Ostmann.ScheduledFrequencyIndex`, `OAI.Ostmann.SurvivingConstituent`, `OAI.Ostmann.copyScheduleOrigin`, `OAI.Ostmann.copyScheduleVertexFintype`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.scheduledFrequencyHistory` and `OAI.Ostmann.transferFrequencyRange` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.naturalTransferCutoff` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.constituentPrimeGuardedAmplitude`, `OAI.Ostmann.constituentPrimeTerm`, `OAI.Ostmann.finalParityReassignmentsFintype`, `OAI.Ostmann.scheduleFourierLeaf` and `OAI.Ostmann.scheduledFrequencyIndexFintype` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedFinalRelativePerm` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.scheduledRootIndex` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_character_final_contradiction` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedFinalNaturalEnergy.lean (declaration OAI.Ostmann.eventual_selected_final_natural_energy_comparison)

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
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_final_natural_energy_comparison (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ M : ℝ in atTop,
    let V := naturalTransferCutoff (d * M) M
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
      (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, role (bulk i).1 = .word)
      (X lo upper : ℝ)
      (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ V (n + 1) < p)
      (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (d * M - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
      (h J : ℕ)
      (_hsmall : V (n + 1) ^ ((2 ^ (n + 2) - 1) * (n + 3)) ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ L : ℝ) (_ha : 0 < a) (_hL : 1 ≤ L)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (center : ∀ p : ℕ, ZMod p) (E : ℝ) (_hE : 0 ≤ E)
      (_hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
        ∀ d d' : ScheduledFrequencyIndex V (n + 1), scheduledRootIndex V (n + 1) d = scheduledRootIndex V (n + 1) d' →
        ‖∑ q : SurvivingConstituent role size (n + 1) → P,
          ((∏ i, primeSubsetPrior P (cells (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
          (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
            childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
            (scheduledFrequencyHistory V (n + 1) d) q *
          conj (constituentPrimeTerm role size χ κ pivot (n + 1) P (fun p hp => (hP p hp).1)
            childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) center
            (scheduledFrequencyHistory V (n + 1) d')
            (fun i => q (selectedFinalRelativePerm (fun i : Σ a, Fin (size a) => role i.1) n m bulk hbulk e f i))))‖ ≤ E),
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P
        (fun p hp => (hP p hp).1) cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V (n + 1)) center‖ ^ 2 ≤
      ((transferFrequencyRange (V (n + 1))).card : ℝ) *
        (Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M) /
          (Fintype.card (FinalParityReassignments n m) : ℝ) +
        (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 * E) := by
  sorry

end Ostmann

end OAI
end
