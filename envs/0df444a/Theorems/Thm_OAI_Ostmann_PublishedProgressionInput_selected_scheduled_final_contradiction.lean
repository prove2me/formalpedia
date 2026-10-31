-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_selected_scheduled_final_contradiction
-- name    : OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:32:43.34227+00:00
-- url     : https://prove2.me/theorems/1c8e66fb-a61f-4774-8417-20aee0dc7125
-- title:
--   OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction` of [lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledFinalContradiction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledFinalContradiction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.selected_scheduled_final_contradiction
--       (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
--       (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Dφ : ℝ)
--       (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hDφ : 0 ≤ Dφ)
--       (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|) :
--       ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 120 ≤ (k : ℝ) ^ 3 →
--       let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
--       ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
--       ∀ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
--       ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
--         spectatorBulkCount k L = b + b → cs.length = k →
--         0 ≤ cb →
--         16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
--         48 * (64 * tailDefectBudget a C Y + 2) ≤ J →
--         (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 →
--         let Q := initialRegularPrimeRange L
--         let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
--         let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
--           (Real.exp ((6 / 1000 : ℝ) * L)) \ D
--         SelectedSmallTailCell Aset Bset N a C L Y endpoint D ((J - 2 * cb) / 6) top →
--         List.Forall₂ (fun j w => SelectedSmallTailCell Aset Bset N a C L Y endpoint D (w / 4) j)
--           cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) →
--         (∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ)) →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
--         smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ L →
--         ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
--         FrozenInitialSpectatorData Aset N q L ε p₀ D →
--         ∀ (sl sr : Fin b → Q) (fallback : Q)
--           (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
--         Monotone V →
--         (V k : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
--         ((transferFrequencyRange (V k)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
--         (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
--         0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
--         Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
--         ∀ favorable : ℕ → Bool,
--         let F := movingOriginalLeaf Subtype.val q
--           (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
--           (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
--           ψ X (Real.exp Δ) upper
--         Real.exp (-B * (2 : ℝ) ^ k * (b + b : ℕ)) ≤
--           ‖scheduledCellAmplitude Subtype.val (List.ofFn q)
--             (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
--             childBound pivotBound V F logCellProfile (fun _ => G)
--             (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
--             (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
--             (primeSubsetPrior Q Qb) top cs k (b + b)
--             (normalizedResidueFamily (tailDensityMask Aset N))
--             (normalizedResidueFamily (tailDensityMask Aset N)) favorable‖ → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.FrozenInitialSpectatorData`, `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MovingSlotState`, `OAI.Ostmann.SelectedSmallTailCell`, `OAI.Ostmann.logCellProfile`, `OAI.Ostmann.primeLogCellSet`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.selectedTailCellPrimes`, `OAI.Ostmann.tailDefectBudget`, `OAI.Ostmann.tailDensityMask`, `OAI.Ostmann.tailResidues` and `OAI.Ostmann.transferFrequencyRange` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.initialRegularPrimeRange`, `OAI.Ostmann.initialSmallCellList`, `OAI.Ostmann.movingCompensationGapRate`, `OAI.Ostmann.movingCompensationGaps`, `OAI.Ostmann.movingCompensationTargets`, `OAI.Ostmann.movingFrequencyRate`, `OAI.Ostmann.negTailResidues`, `OAI.Ostmann.scheduledComparisonCutoff`, `OAI.Ostmann.smoothGiantLogNormalizer`, `OAI.Ostmann.smoothGiantPrimeRange`, `OAI.Ostmann.smoothGiantPrior`, `OAI.Ostmann.spectatorBaseGap` and `OAI.Ostmann.spectatorBulkCount` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.completedCompensationPrior`, `OAI.Ostmann.initialMovingDataCutoff` and `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.normalizedResidueFamily` and `OAI.Ostmann.scheduledCellAmplitude` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.movingOriginalLeaf` and `OAI.Ostmann.scheduledPageDeletions` (definitions bundle `OAIQ095D008` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/SelectedScheduledFinalContradiction.lean (declaration OAI.Ostmann.PublishedProgressionInput.selected_scheduled_final_contradiction)

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

theorem PublishedProgressionInput.selected_scheduled_final_contradiction
    (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Dφ : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hDφ : 0 ≤ Dφ)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|) :
    ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 120 ≤ (k : ℝ) ^ 3 →
    let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
    ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
    ∀ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
    ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
      spectatorBulkCount k L = b + b → cs.length = k →
      0 ≤ cb →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      48 * (64 * tailDefectBudget a C Y + 2) ≤ J →
      (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 →
      let Q := initialRegularPrimeRange L
      let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      SelectedSmallTailCell Aset Bset N a C L Y endpoint D ((J - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell Aset Bset N a C L Y endpoint D (w / 4) j)
        cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) →
      (∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ)) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ L →
      ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
      FrozenInitialSpectatorData Aset N q L ε p₀ D →
      ∀ (sl sr : Fin b → Q) (fallback : Q)
        (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
      Monotone V →
      (V k : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      ((transferFrequencyRange (V k)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
      Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
      ∀ favorable : ℕ → Bool,
      let F := movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
        (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
        ψ X (Real.exp Δ) upper
      Real.exp (-B * (2 : ℝ) ^ k * (b + b : ℕ)) ≤
        ‖scheduledCellAmplitude Subtype.val (List.ofFn q)
          (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
          childBound pivotBound V F logCellProfile (fun _ => G)
          (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs k (b + b)
          (normalizedResidueFamily (tailDensityMask Aset N))
          (normalizedResidueFamily (tailDensityMask Aset N)) favorable‖ → False := by
  sorry

end Ostmann

end OAI
end
