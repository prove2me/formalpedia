-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_pattern_diagonal_haar_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:31:12.715364+00:00
-- url     : https://prove2.me/theorems/398199a4-e348-40c4-89cd-331901700924
-- title:
--   OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalHaarComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalHaarComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.moving_pattern_diagonal_haar_rate
--       (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (B C J : Type) [Fintype C] [Fintype J] (N : ℕ)
--           (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
--           (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
--           (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
--           (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) (x : Fin (N + 1) → primes)
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
--           (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
--           (active : J → Bool) (sreg : ℤ) (other : ∀ j, ZMod (reg j))
--           (greg : ∀ j, ZMod (reg j) → ℂ)
--           (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
--           (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
--           [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
--           [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
--           (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
--           (V : ℕ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool),
--         let value := fun i => (x i : ℕ)
--         let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
--         let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
--         let Reg := MovingSlotReversal.naturalProduct value
--           (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
--             flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
--         (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
--         (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → value i ≠ value j) →
--         (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) → (∀ i, V < value i) →
--         (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
--         (∀ q ∈ outside, ∃ i, p i = q) →
--         (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
--         (∀ i, IsCoprime (value i : ℤ) R) →
--         (∀ i j, (value j : ZMod (p i)) ≠ 0) → (∀ i, V < p i) →
--         P = Finset.univ.image (fun c : C => value (e.symm (.inr c))) →
--         Function.Injective (fun c : C => value (e.symm (.inr c))) →
--         Pairwise (fun a b => (movingArithmeticModuli r p P Finset.univ a).Coprime
--           (movingArithmeticModuli r p P Finset.univ b)) →
--         Reg = ∏ j, reg j → Reg.Coprime M → Reg * M ≤ giantProgressionCutoff L →
--         pageAtModulus (Reg * M) (selectedPageZero input (giantProgressionCutoff L)) =
--           pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) →
--         pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) =
--           pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) →
--         (∀ b, movingRegularOutsidePairwise value outside (T b)) →
--         Pairwise (fun i j => (reg i).Coprime (reg j)) →
--         (∀ i, (∏ j, reg j).Coprime (p i)) →
--         (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
--         (∀ i, greg i 0 = 0) → (∀ i, (∑ z : ZMod (reg i), ‖greg i z‖ ^ 2) = reg i) →
--         (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
--         (∀ z, 1 ≤ |z| → φ z = 0) →
--         ∀ u v a b center : ℝ,
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
--         ‖complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
--             movingOriginalSupportedOuterPair p value outside childBound pivotBound
--               (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
--               ψ X lo hi φ G Jleft Jright diagonal T t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
--             (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
--           (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
--             ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
--               (((∏ j, if active j then (1 : ℝ) else 1 - (reg j : ℝ)⁻¹) : ℝ) : ℂ)) *
--               movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
--                 primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
--                 (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
--                 (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
--               (Real.exp (z - center) : ℂ) / (y : ℂ)) *
--             movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
--               n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
--           Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
--             Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingArithmeticBlocks`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.MovingSlotData.frequencyProduct` and `OAI.Ostmann.MovingSlotReversal.naturalProduct` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.complexIntegerInterval`, `OAI.Ostmann.complexPrimeInterval`, `OAI.Ostmann.giantProgressionCutoff`, `OAI.Ostmann.naturalRegularMultiplier` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.bulkSlotLeaves`, `OAI.Ostmann.giantOuterWeight`, `OAI.Ostmann.movingArithmeticModuli`, `OAI.Ostmann.movingRegularOutsidePairwise` and `OAI.Ostmann.pageAtModulus` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingPatternFiniteSmall` and `OAI.Ostmann.movingSampleTier` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingPatternBulkLeaves` and `OAI.Ostmann.movingPatternFinBulkData` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalSupportedOuterPair`, `OAI.Ostmann.movingPatternHaarProduct` and `OAI.Ostmann.movingPatternPrimeObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_whole_shell_masked_rate` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternDiagonalHaarComparison.lean (declaration OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate)

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

theorem PublishedProgressionInput.moving_pattern_diagonal_haar_rate
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C J : Type) [Fintype C] [Fintype J] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) (x : Fin (N + 1) → primes)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
        (active : J → Bool) (sreg : ℤ) (other : ∀ j, ZMod (reg j))
        (greg : ∀ j, ZMod (reg j) → ℂ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
        [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
        [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (V : ℕ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool),
      let value := fun i => (x i : ℕ)
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
      let Reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → value i ≠ value j) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) → (∀ i, V < value i) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, IsCoprime (value i : ℤ) R) →
      (∀ i j, (value j : ZMod (p i)) ≠ 0) → (∀ i, V < p i) →
      P = Finset.univ.image (fun c : C => value (e.symm (.inr c))) →
      Function.Injective (fun c : C => value (e.symm (.inr c))) →
      Pairwise (fun a b => (movingArithmeticModuli r p P Finset.univ a).Coprime
        (movingArithmeticModuli r p P Finset.univ b)) →
      Reg = ∏ j, reg j → Reg.Coprime M → Reg * M ≤ giantProgressionCutoff L →
      pageAtModulus (Reg * M) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) →
      pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) →
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ z : ZMod (reg i), ‖greg i z‖ ^ 2) = reg i) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      ∀ u v a b center : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      ‖complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound
            (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
            ψ X lo hi φ G Jleft Jright diagonal T t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
          (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
          ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
            (((∏ j, if active j then (1 : ℝ) else 1 - (reg j : ℝ)⁻¹) : ℝ) : ℂ)) *
            movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
              primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
              (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
              (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  sorry

end Ostmann

end OAI
end
