-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_original_mixed_prime_norm_arithmetic_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:29:07.046702+00:00
-- url     : https://prove2.me/theorems/bbc48eef-1494-4880-88b8-0101a1fe58d7
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedOriginalNormArithmetic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedOriginalNormArithmetic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate
--       (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (A Wwin Bφ Dφ F Cmass : ℝ)
--       (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
--         hi - lo ≤ Real.exp (Wwin * m) →
--         ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
--           (t : Bool → FrequencyTree ℤ n)
--           (small : Bool → TreeLeafTuple (List Bidx) n)
--           (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
--           (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
--           (pattern : Bool × MovingSampleIndex n → Cidx)
--           (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
--           (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
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
--           (deleted : (Fin (N + 1) → primes) →
--             (TreeLeafIndex n × Fin m) → Finset ℕ)
--           (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
--           (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
--           (W : (Fin (N + 1) → primes) → ℂ) (Eprior αall βint Vint Uall : ℝ),
--         let data := movingPatternFinBulkData e n m t small slot perm pattern
--         let M := ∏ i, bulkResidueModuli r p i
--         let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
--           (fun c => u j c.1) (fun c => v j c.1)
--         let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
--           ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
--         let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
--         let raw := movingPatternPrimeObservable e t small slot perm pattern primes hprimes
--           childBound pivotBound hfreq Fw Ew outside R r p
--           (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
--           y ψ X lo hi hlo hhi φ G XL U
--         let obs := fun x => W x * raw x
--         let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
--           (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
--             (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
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
--         (∀ x, productPrior law x ≠ 0 →
--           ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
--         (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
--         (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
--           ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
--         (∀ q ∈ outside, q.Prime) →
--         (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
--         0 ≤ A₀ →
--         (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
--           let freq := frozenBulkFrequencyFactor (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot)
--             outside Fw Ew data childBound R r P Qfreq y
--           let spec := fun i => frozenBulkSpectatorHaar (fun i => (x i : ℕ)) n m t
--             (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
--             (twist i) perm (normalizedResidueTransform (sets i))
--           let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
--             ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
--           ∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
--             (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
--               ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
--                 (w j).val.val (z j)‖ ≤ A₀) →
--         ∀ _c₀ : Cell × (ZMod M)ˣ,
--         (∀ j, initial j ⊆ S j) →
--         (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
--         (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
--         (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
--         (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
--         0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
--         (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
--         (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
--         (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
--         (∀ q : primes, (q : ℝ) ≤ Uall) →
--         (∀ x, ‖W x‖ ≤ 1) →
--         (∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x) →
--         (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
--           (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
--             (x i : ℕ) ≠ (x j : ℕ)) →
--         (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
--           (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
--         (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
--           (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
--         ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern obs x *
--           movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
--             n t small (movingPatternBulkLeaves n m slot perm) pattern x‖ ≤
--         ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
--           (cost * movingInternalArithmeticError n (Fintype.card Cidx)
--             (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
--           ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
--             Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
--             2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.treeLeafIndexFintype`, `OAI.Ostmann.MovingSlotData.Frequencies` and `OAI.Ostmann.MovingSlotData.frequencyProduct` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.bulkResidueEquiv`, `OAI.Ostmann.bulkResidueModuli`, `OAI.Ostmann.joinBulkNonbulk`, `OAI.Ostmann.movingFourierVariationBudget`, `OAI.Ostmann.movingInternalArithmeticError`, `OAI.Ostmann.productPrior` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.frozenBulkSpectatorHaar`, `OAI.Ostmann.movingDataWeight`, `OAI.Ostmann.normalizedResidueTransform` and `OAI.Ostmann.treeLeafIndexDecidableEq` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingPatternFiniteSmall`, `OAI.Ostmann.movingSampleTier` and `OAI.Ostmann.primeCellSupport` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.frozenBulkFrequencyFactor` and `OAI.Ostmann.pageGiantWeight` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingOriginalPatternWeight`, `OAI.Ostmann.movingPatternBulkLeaves`, `OAI.Ostmann.movingPatternFinBulkData` and `OAI.Ostmann.movingPatternFiniteSamples` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingPatternHaarProduct` and `OAI.Ostmann.movingPatternPrimeObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedOriginalNormArithmetic.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate)

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

theorem PublishedProgressionInput.movingPattern_original_mixed_prime_norm_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
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
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (W : (Fin (N + 1) → primes) → ℂ) (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G XL U
      let obs := fun x => W x * raw x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
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
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      0 ≤ A₀ →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        let freq := frozenBulkFrequencyFactor (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot)
          outside Fw Ew data childBound R r P Qfreq y
        let spec := fun i => frozenBulkSpectatorHaar (fun i => (x i : ℕ)) n m t
          (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
          (twist i) perm (normalizedResidueTransform (sets i))
        let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
          ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
        ∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
          (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
            ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
              (w j).val.val (z j)‖ ≤ A₀) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, ‖W x‖ ≤ 1) →
      (∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern obs x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          n t small (movingPatternBulkLeaves n m slot perm) pattern x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  sorry

end Ostmann

end OAI
end
