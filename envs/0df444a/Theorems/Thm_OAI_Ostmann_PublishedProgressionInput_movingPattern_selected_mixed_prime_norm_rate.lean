-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_selected_mixed_prime_norm_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:30:26.273357+00:00
-- url     : https://prove2.me/theorems/3357ae4e-37c0-4f6e-834c-6a61be7269e9
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeSelectedNormRate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeSelectedNormRate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate
--       (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (A Wwin Bφ Dφ F Cmass : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
--         hi - lo ≤ Real.exp (Wwin * m) →
--         ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
--           (t : Bool → FrequencyTree ℤ n)
--           (small : Bool → TreeLeafTuple (List Bidx) n)
--           (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
--           (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
--           (pattern : Bool × MovingSampleIndex n → Cidx)
--           (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
--           (base : Fin (N + 1) → primes)
--           (childBound pivotBound : ℕ → ℕ)
--           (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
--           (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
--           (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
--           (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
--           [NeZero (∏ i, bulkResidueModuli r p i)]
--           (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (Qfreq : ℕ) (y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
--           (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
--           (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ),
--         let data := movingPatternFinBulkData e n m t small slot perm pattern
--         let M := ∏ i, bulkResidueModuli r p i
--         let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
--           (fun c => u j c.1) (fun c => v j c.1)
--         let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
--           ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
--         let freq := frozenBulkFrequencyFactor (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) outside
--           Fw Ew data childBound R r P Qfreq y
--         let spec := fun i => frozenBulkSpectatorHaar (fun i => (base i : ℕ)) n m t
--           (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
--           (twist i) perm (normalizedResidueTransform (sets i))
--         let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
--           ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
--         (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
--         (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
--         (∀ b, MovingLeafLengthLE n (small b) r₀) →
--         (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
--         (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         amp ≤ Real.exp (F * m) → 0 ≤ y →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         M ≤ bulkProgressionCutoff L →
--         (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
--         (∀ x, 1 ≤ |x| → φ x = 0) →
--         (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
--         (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
--         (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
--         (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
--         (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
--         (∀ j, S j ⊆ primes) →
--         (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
--         (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
--         (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (base i : ℕ) ∈ deleted j) →
--         (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
--         0 ≤ A₀ →
--         (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
--           (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
--             ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
--               (w j).val.val (z j)‖ ≤ A₀) →
--         ∀ _c₀ : Cell × (ZMod M)ˣ,
--         ∀ initial : (TreeLeafIndex n × Fin m) → Finset ℕ,
--         (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
--         ∀ ν : Bidx → primes → ℝ,
--         (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
--         ‖movingPatternBulkMean e ν slot
--           (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
--             childBound pivotBound hfreq Fw Ew outside R r p
--             (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
--             y ψ X lo hi hlo hhi φ G XL U) base‖ ≤
--           ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
--             Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
--             Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
--             2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.treeLeafIndexFintype` and `OAI.Ostmann.MovingSlotData.frequencyProduct` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.bulkResidueEquiv`, `OAI.Ostmann.bulkResidueModuli` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.frozenBulkSpectatorHaar`, `OAI.Ostmann.movingDataWeight`, `OAI.Ostmann.normalizedResidueTransform` and `OAI.Ostmann.treeLeafIndexDecidableEq` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingPatternFiniteSmall`, `OAI.Ostmann.movingSampleTier` and `OAI.Ostmann.primeCellSupport` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.frozenBulkFrequencyFactor` and `OAI.Ostmann.pageGiantWeight` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingPatternBulkMean`, `OAI.Ostmann.movingPatternFinBulkData` and `OAI.Ostmann.movingPatternFiniteSamples` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingPatternPrimeObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeSelectedNormRate.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate)

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

theorem PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (base : Fin (N + 1) → primes)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let freq := frozenBulkFrequencyFactor (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) outside
        Fw Ew data childBound R r P Qfreq y
      let spec := fun i => frozenBulkSpectatorHaar (fun i => (base i : ℕ)) n m t
        (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
        (twist i) perm (normalizedResidueTransform (sets i))
      let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
        ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (base i : ℕ) ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      0 ≤ A₀ →
      (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
        (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
          ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
            (w j).val.val (z j)‖ ≤ A₀) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ∀ initial : (TreeLeafIndex n × Fin m) → Finset ℕ,
      (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
      ∀ ν : Bidx → primes → ℝ,
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      ‖movingPatternBulkMean e ν slot
        (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
          childBound pivotBound hfreq Fw Ew outside R r p
          (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
          y ψ X lo hi hlo hhi φ G XL U) base‖ ≤
        ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  sorry

end Ostmann

end OAI
end
