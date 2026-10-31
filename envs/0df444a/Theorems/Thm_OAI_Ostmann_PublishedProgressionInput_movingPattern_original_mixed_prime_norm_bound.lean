-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_original_mixed_prime_norm_bound
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:30:08.593177+00:00
-- url     : https://prove2.me/theorems/c8ff2b4a-078a-4f3c-a9fa-6301f7c55d8d
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeNormBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeNormBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound
--       [NeZero (∏ i, bulkResidueModuli r p i)]
--       (r₀ : ℕ) (hsmallLen : ∀ b, MovingLeafLengthLE n (small b) r₀)
--       (hy : 0 ≤ y) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
--       (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
--       (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
--       (hshort : ∀ j c, v j c ≤ u j c + 1)
--       (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
--         ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
--           (q : ℝ)⁻¹ ≤ 2)
--       (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
--       (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
--         (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
--         (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
--       (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
--         ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
--           v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
--       (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
--       (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
--         (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
--         (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
--       (hdeletedBase : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
--       (hout : ∀ q ∈ outside, q.Prime) (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j)
--       (Kspec : Fin m → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
--       (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
--       (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (H T : ℝ) :
--       let data := movingPatternFinBulkData e n m t small slot perm pattern
--       let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
--         F E data childBound R r P Qfreq y
--       let spec := fun i => frozenBulkSpectatorHaar base n m t
--         (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
--         (twist i) perm (g i)
--       let A := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
--         ‖movingDataWeight (F true) (E true) (data true)‖)
--       let W := (movingFourierVariationBudget ψ V lo hi n *
--         (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
--       let W₀ := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2
--       let M := ∏ i, bulkResidueModuli r p i
--       let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
--         (fun c => u j c.1) (fun c => v j c.1)
--       let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
--       let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
--         ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
--       let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
--         2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
--           bulkKernelPairComparisonBudget ψ V lo hi n
--             (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
--             bulkPrimeErrorFactor P Q (u j (c j))
--       (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
--         (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
--           ∑ w, ‖a w * ∏ j, pageGiantWeight P Q M (w j).val.val (z j)‖ ≤ A₀) →
--       (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
--       (∀ j, Z j ≤ Real.exp H) →
--       (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
--       ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
--         ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
--           movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
--             childBound pivotBound hfreq F E outside R r p g twist P Qfreq y ψ X lo hi hlo hhi φ G L U x‖ ≤
--         (W₀ * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
--           (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
--           (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
--             (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
--           (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
--             ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.treeLeafIndexFintype` and `OAI.Ostmann.MovingSlotData.frequencyProduct` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkKernelPairComparisonBudget`, `OAI.Ostmann.bulkResidueEquiv`, `OAI.Ostmann.bulkResidueModuli` and `OAI.Ostmann.movingFourierVariationBudget` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.frozenBulkSpectatorHaar`, `OAI.Ostmann.movingDataWeight` and `OAI.Ostmann.treeLeafIndexDecidableEq` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingPatternFiniteSmall`, `OAI.Ostmann.movingSampleTier` and `OAI.Ostmann.primeCellSupport` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.bulkPrimeErrorFactor`, `OAI.Ostmann.frozenBulkFrequencyFactor` and `OAI.Ostmann.pageGiantWeight` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingPatternFinBulkData` and `OAI.Ostmann.movingPatternFiniteSamples` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingPatternPrimeBulkHaar` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternMixedPrimeNormBound.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound)

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
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell : Type*} [Fintype Cell] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q Qfreq : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hsmall hB htier hR hr hg hV hBφ hDφ hφ hlip hφout j₀ in
theorem PublishedProgressionInput.movingPattern_original_mixed_prime_norm_bound
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (r₀ : ℕ) (hsmallLen : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (hy : 0 ≤ y) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
    (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
    (hshort : ∀ j c, v j c ≤ u j c + 1)
    (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
      ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
        (q : ℝ)⁻¹ ≤ 2)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (hdeletedBase : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
    (hout : ∀ q ∈ outside, q.Prime) (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j)
    (Kspec : Fin m → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (H T : ℝ) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F E data childBound R r P Qfreq y
    let spec := fun i => frozenBulkSpectatorHaar base n m t
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) perm (g i)
    let A := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    let W₀ := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
    let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u j (c j))
    (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
      (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ w, ‖a w * ∏ j, pageGiantWeight P Q M (w j).val.val (z j)‖ ≤ A₀) →
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
          childBound pivotBound hfreq F E outside R r p g twist P Qfreq y ψ X lo hi hlo hhi φ G L U x‖ ≤
      (W₀ * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  sorry

end
end Ostmann

end OAI
end
