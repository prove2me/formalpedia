-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_diagonal_whole_shell_masked_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:26:44.664183+00:00
-- url     : https://prove2.me/theorems/41f8ce32-62bd-4591-b12b-4fd7057558da
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalMaskedShell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalMaskedShell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate
--       (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (A Wwin Bφ Dφ Cmass : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
--         hi - lo ≤ Real.exp (Wwin * m) →
--         ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
--           (t : Bool → FrequencyTree ℤ n)
--           (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
--           (small : TreeLeafTuple (List Bidx) n)
--           (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
--           (pattern : Bool × MovingSampleIndex n → Cidx)
--           (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
--           (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (childBound pivotBound : ℕ → ℕ)
--           (f : ℤ → ℂ)
--           (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
--           [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
--           (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (global : Finset ℕ)
--           (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
--           (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
--           (Eprior αall βint Vint Uall : ℝ)
--           (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
--           (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
--         let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
--         let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
--           (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
--             ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
--         let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
--         let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L))
--         1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
--         (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
--         (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
--         (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
--         t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
--         (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
--         (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
--         0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
--         0 < m → (∀ i, 3 ≤ p i) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         M ≤ bulkProgressionCutoff L →
--         (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) →
--         S ⊆ primes →
--         ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
--         (∀ q ∈ outside, q.Prime) →
--         (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
--         (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
--         (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
--         1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
--         (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
--         (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
--         (∀ q : primes, (q : ℝ) ≤ Uall) →
--         (∀ j, active j = false →
--           (movingPatternRegularSlots e n m small slot).get j ∉
--             Set.range (movingPatternBulkEmbedding e slot)) →
--         (∀ q ∈ outside, ∃ i, p i = q) →
--         Function.Injective p →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
--         (Nfreq : ℝ) ≤ Real.exp (A * m) →
--         Eprior ≤ Real.exp (Cmass * L) →
--         αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
--         βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
--         Vint = Real.exp ((1 / 100 : ℝ) * L) →
--         Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
--         Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
--         (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
--         (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
--         Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
--         (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
--         (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
--         (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
--         (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q →
--           ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
--         (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
--           deletedConductorPrime z.modulus cutoff = some q →
--           ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
--         sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
--         (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
--         ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
--           (movingOriginalPatternDiagonalObservable e t small slot pattern primes _hprimes
--             p (fun i => normalizedResidueTransform (sets i)) Dq
--             (movingPatternRegularSlots e n m small slot).get active sreg
--             (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
--               (movingPatternRegularSlots e n m small slot))
--             (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
--             Jleft Jright diagonal uG vG rG sG center) x‖ ≤
--           ((2 : ℝ) ^ Fintype.card Cidx *
--             (Real.exp (Cmass * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
--             (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
--                 Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
--                   2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
--               Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
--               4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.NodeFrequencies`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior` and `OAI.Ostmann.treeLeafIndexFintype` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.bulkResidueModuli`, `OAI.Ostmann.deletedConductorPrime`, `OAI.Ostmann.giantProgressionCutoff`, `OAI.Ostmann.movingRegularOther`, `OAI.Ostmann.pairedFrequencyLeaf` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.frequencyLeafWeight`, `OAI.Ostmann.frequencyModelBase`, `OAI.Ostmann.frequencyPairProjection`, `OAI.Ostmann.frequencySplitList`, `OAI.Ostmann.frequencyTreeMap` and `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingSampleTier` and `OAI.Ostmann.pairFrequencySupportBound` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingOriginalPatternWeight`, `OAI.Ostmann.movingPatternRegularSlots` and `OAI.Ostmann.normalizedResidueFamily` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalPatternDiagonalObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.PublishedProgressionInput.moving_selected_amplitude_regular_energy`, `OAI_Ostmann_PublishedProgressionInput_moving_selected_initial_full_energy` and `OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalMaskedShell.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate)

import Mathlib
import Definitions.Def_OAIQ095D008

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (Eprior αall βint Vint Uall : ℝ)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e n m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Eprior ≤ Real.exp (Cmass * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e n m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          (Real.exp (Cmass * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
              Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
                2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  sorry

end Ostmann

end OAI
end
