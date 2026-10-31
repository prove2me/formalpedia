-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_amplitude_regular_energy
-- name    : OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:20.602366+00:00
-- url     : https://prove2.me/theorems/5fc326eb-deb0-49bd-aa93-4f82559e6127
-- title:
--   OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedAmplitudeEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedAmplitudeEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.moving_selected_amplitude_regular_energy
--       (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
--       (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n ≤ k)
--       (A Wwin Bφ Dφ c K ε : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
--       (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
--       (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         let Cprior := K + 1
--         ∀ (tierB : MovingRegularSlot n r m → ℕ)
--           (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
--           (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
--           (setsReg : ∀ q : ℕ, Finset (ZMod q)),
--         let H := G (n + 1)
--         let slot := movingTemplateBulk n r m
--         let μ := fun j => primeSubsetPrior primes (Qμ j)
--         let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L))
--         let Sfreq := (transferFrequencyRange (V n)).erase 0
--         Monotone V → f 0 = 0 →
--         (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
--         (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
--         (V n : ℝ) ≤ Real.exp (A * m) →
--         (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
--         0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
--         1 ≤ H - 1 →
--         (∀ i, n ≤ tierB i) →
--         0 < m → (∀ i, 3 ≤ p i) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
--         ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
--         (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
--         (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
--         (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
--         (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
--         (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
--         V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
--         (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
--         (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
--         (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
--         (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
--         (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp b) →
--         movingAmplitudeRegularEnergy primes (smoothGiantPrimeRange H)
--           (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊) outside μ childBound pivotBound V
--           (movingOriginalLeaf Subtype.val p (fun _ => f) (fun i => normalizedResidueTransform (sets i))
--             Dq Finset.univ ψ X (Real.exp Δ) hi) φ G n r m Qν (normalizedResidueFamily setsReg) ≤
--         Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
--           smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
--           (4 * (Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
--             5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingRegularSlot`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.movingTemplateBulk`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.transferFrequencyRange` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.deletedConductorPrime`, `OAI.Ostmann.giantProgressionCutoff`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantPrimeRange` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.movingAmplitudeRegularEnergy` and `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform` and `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_early_log_diagonal` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedAmplitudeEnergy.lean (declaration OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy)

import Mathlib
import Definitions.Def_OAIQ095D008

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_amplitude_regular_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q)),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, n ≤ tierB i) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp b) →
      movingAmplitudeRegularEnergy primes (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊) outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p (fun _ => f) (fun i => normalizedResidueTransform (sets i))
          Dq Finset.univ ψ X (Real.exp Δ) hi) φ G n r m Qν (normalizedResidueFamily setsReg) ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
        (4 * (Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) := by
  sorry

end Ostmann

end OAI
end
