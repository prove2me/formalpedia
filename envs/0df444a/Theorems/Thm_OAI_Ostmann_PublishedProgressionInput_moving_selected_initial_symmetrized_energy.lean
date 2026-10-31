-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_symmetrized_energy
-- name    : OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:31:23.216676+00:00
-- url     : https://prove2.me/theorems/7ee69247-044b-40a7-919e-b8fbd1d97588
-- title:
--   OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedInitialSymmetrization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedInitialSymmetrization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.moving_selected_initial_symmetrized_energy
--       (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
--       (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
--       (A Wwin Bφ Dφ c K εdiag gain : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
--       (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
--       (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
--       (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
--       (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
--       ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
--         let m := b + b
--         let Cprior := K + 1
--         ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
--           (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
--           (childBound pivotBound V : ℕ → ℕ)
--           (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (β : Fin m → ℝ)
--           (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (active : MovingRegularSlot (n + 2) r₀ m → Bool)
--           (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
--           (setsReg : ∀ q : ℕ, Finset (ZMod q))
--           (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center cb cd : ℝ),
--         let slot := movingTemplateBulk (n + 2) r₀ m
--         let μ := fun j => primeSubsetPrior primes (Qμ j)
--         let ν := fun j => primeSubsetPrior primes (Qν j)
--         let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L))
--         let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
--         r₀ + 4 * (n + 2) = r + r →
--         Monotone V →
--         (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
--         (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
--         (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
--         0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
--         1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
--         (∀ i, (n + 2) ≤ tierB i) →
--         1 ≤ m → (∀ i, primeCutoff ≤ p i) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
--         (∀ i, residueDensity (sets i) ≤ 2 / 3) →
--         (∀ i, 2 * β i ≤ ε) →
--         (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
--           ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
--         (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
--         ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
--         (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
--         (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
--         (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
--         (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
--         (∀ j, active (slot j) = true) →
--         (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
--         (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
--         (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
--         V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
--         (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
--         (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
--         (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
--         (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
--         ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
--           (movingOriginalLeaf Subtype.val p
--             (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
--             (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
--           φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
--           Jleft Jright diagonal uG vG rG sG center‖ ≤
--         (((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
--           Real.exp ((2 ^ (n + 2) : ℝ) * m *
--             (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
--           (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
--             (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
--               5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
--           Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingRegularSlot`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.movingTemplateBulk`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.transferFrequencyRange` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.deletedConductorPrime`, `OAI.Ostmann.giantProgressionCutoff` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.initialMovingDataCutoff` and `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingTemplateMaskedSymmetrizedEnergy` and `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_diagonal_uniform` and `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingSelectedInitialSymmetrization.lean (declaration OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy)

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
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_symmetrized_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center cb cd : ℝ),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
        Jleft Jright diagonal uG vG rG sG center‖ ≤
      (((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  sorry

end Ostmann

end OAI
end
