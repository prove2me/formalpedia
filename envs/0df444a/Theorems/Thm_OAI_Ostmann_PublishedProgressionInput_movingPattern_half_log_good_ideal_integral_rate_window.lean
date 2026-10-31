-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_half_log_good_ideal_integral_rate_window
-- name    : OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:27:00.971343+00:00
-- url     : https://prove2.me/theorems/9966d9a1-3707-4325-9f67-187dd6ab1a20
-- title:
--   OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodIdealIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodIdealIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window
--       (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
--       (A H Bφ Dφ F Cmass gain : ℝ)
--       (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
--       (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
--       (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
--       (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
--       (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
--       ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
--         ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
--         ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
--           (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
--           (t : Bool → FrequencyTree ℤ (n + 2))
--           (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
--           (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
--           (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
--           (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
--           (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
--           (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
--           (childBound pivotBound : ℕ → ℕ)
--           (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
--           (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
--           (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
--           (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
--           (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
--           (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
--           [NeZero (∏ i, bulkResidueModuli r p i)]
--           (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
--           (β : Fin m → ℝ) (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
--           (φ : ℝ → ℝ) (G : ℕ → ℝ)
--           (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
--           (deleted : (Fin (N + 1) → primes) →
--             (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
--           (initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
--           (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
--           (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
--           (Jidx : Type) [Fintype Jidx] (reg : Jidx → Fin (N + 1)) (active : Jidx → Bool)
--           (Jleft Jright : ℝ) (diagonal : Bool)
--           (Eprior αall βint Vint Uall uG vG rG sG center : ℝ),
--         let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
--         let M := ∏ i, bulkResidueModuli r p i
--         let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
--           (fun c => u j c.1) (fun c => v j c.1)
--         let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
--           ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
--         let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
--         let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
--           childBound pivotBound hfreq Fw Ew outside R r p
--           (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
--           y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
--         let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ Jleft Jright Bφ Dφ diagonal
--         let obs := fun xg y x => W xg y x * raw xg y x
--         let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
--           (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
--             (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
--         (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
--         1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
--         1 ≤ m →
--         (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
--         (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
--         (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
--         (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
--         (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
--         (∀ i, cutoff ≤ p i) →
--         (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
--         (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
--           ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
--             ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
--         (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
--           ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
--         4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
--           3 * Fintype.card (TreeLeafIndex (n + 2)) →
--         (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
--         (∀ i, residueDensity (sets i) ≤ 2 / 3) →
--         (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
--         (∀ i, 2 * β i ≤ ε) →
--         (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
--           ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
--         amp ≤ Real.exp (F * m) →
--         (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
--         M ≤ bulkProgressionCutoff L →
--         pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
--           pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
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
--         (∀ j, active j = false → reg j ∉ Set.range (movingPatternBulkEmbedding e slot)) →
--         (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
--           (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
--             (x i : ℕ) ≠ (x j : ℕ)) →
--         (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
--           (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
--         (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
--           (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
--         ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
--             (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
--               ((giantOuterWeight φ Jleft Jright diagonal (Real.exp xg) (Real.exp y) *
--                 (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) * raw xg y x) * (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
--           movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
--             (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
--         diagonalOuterMajorant Bφ Dφ diagonal * ((2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
--           (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
--             (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
--           (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
--             2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PrimitiveRealZero` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.MovingLeafLengthLE`, `OAI.Ostmann.MovingSampleIndex`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.arrangementGraph`, `OAI.Ostmann.flattenMovingSlots`, `OAI.Ostmann.instFintypeConnectedComponentSumArrangementGraph`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.treeLeafIndexFintype`, `OAI.Ostmann.MovingSlotData.Frequencies` and `OAI.Ostmann.MovingSlotData.frequencyProduct` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.bulkProgressionCutoff`, `OAI.Ostmann.bulkResidueModuli`, `OAI.Ostmann.diagonalOuterMajorant`, `OAI.Ostmann.inactiveRegularDensity`, `OAI.Ostmann.movingFourierVariationBudget`, `OAI.Ostmann.movingInternalArithmeticError`, `OAI.Ostmann.productPrior` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.giantOuterWeight`, `OAI.Ostmann.movingDataWeight`, `OAI.Ostmann.movingDiagonalOuterWeight`, `OAI.Ostmann.normalizedResidueTransform` and `OAI.Ostmann.pageAtModulus` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.movingPatternBulkEmbedding`, `OAI.Ostmann.movingSampleTier` and `OAI.Ostmann.primeCellSupport` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.selectedPageZero` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingOriginalPatternWeight`, `OAI.Ostmann.movingPatternBulkLeaves` and `OAI.Ostmann.movingPatternFinBulkData` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingPatternHaarProduct` and `OAI.Ostmann.movingPatternLogPrimeObservable` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_masked_whole_shell_rate` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingPatternHalfLogGoodIdealIntegral.lean (declaration OAI.Ostmann.PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window)

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

theorem PublishedProgressionInput.movingPattern_half_log_good_ideal_integral_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (Jidx : Type) [Fintype Jidx] (reg : Jidx → Fin (N + 1)) (active : Jidx → Bool)
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall uG vG rG sG center : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := fun xg y => movingPatternLogPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y) logSlots cb
      let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ Jleft Jright Bφ Dφ diagonal
      let obs := fun xg y x => W xg y x * raw xg y x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
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
      (∀ j, active j = false → reg j ∉ Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
          (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
            ((giantOuterWeight φ Jleft Jright diagonal (Real.exp xg) (Real.exp y) *
              (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) * raw xg y x) * (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * ((2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) := by
  sorry

end Ostmann

end OAI
end
