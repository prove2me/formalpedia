-- Prove2me | Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_outer_coprime_mixed_haar_rate
-- name    : OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:09.040568+00:00
-- url     : https://prove2.me/theorems/2881e1cf-19a8-4413-9108-40e964ea41b6
-- title:
--   OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate` of [lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingOuterCoprimeComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingOuterCoprimeComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter MeasureTheory`, `open scoped BigOperators Classical SchwartzMap`):
--
--   ```lean
--   theorem PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate (P : PublishedProgressionInput)
--       (n : ℕ) (C : ℝ) (d : ℕ) :
--       ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
--         (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
--         (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
--         (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
--         (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
--         (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
--         ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
--         Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
--         ∀ u v r s J : ℝ,
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
--         Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
--         Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
--         ∀ c : ℕ → ℕ → ℂ,
--         ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
--         2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
--           Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
--         letI : NeZero q := ⟨by omega⟩
--         let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
--         ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
--             if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then
--               c (⌊Real.exp x⌋₊ % q) (⌊Real.exp y⌋₊ % q) *
--                 movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
--             else 0)) -
--           (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
--             movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
--               (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
--           Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MovingFormulaNode`, `OAI.Ostmann.MovingSlotData`, `OAI.Ostmann.HistoryFormula`, `OAI.Ostmann.MovingSlotData.Frequencies` and `OAI.Ostmann.MovingSlotData.formulaNodes` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.complexIntegerInterval`, `OAI.Ostmann.complexPrimeInterval`, `OAI.Ostmann.giantOuterScalar` and `OAI.Ostmann.movingOuterVariationBudget` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.correctedMixedPairAverage` (definitions bundle `OAIQ095D006` of this split); `OAI.Ostmann.movingOuterKernel` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proofs of `OAI_Ostmann_PublishedProgressionInput_movingPattern_original_diagonal_norm`, `OAI_Ostmann_PublishedProgressionInput_movingPattern_weighted_original_matched_norm`, `OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate` and `OAI.Ostmann.PublishedProgressionInput.moving_pattern_matched_haar_rate` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Arithmetic/MovingOuterCoprimeComparison.lean (declaration OAI.Ostmann.PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate)

import Mathlib
import Definitions.Def_OAIQ095D006
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_coprime_mixed_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then
            c (⌊Real.exp x⌋₊ % q) (⌊Real.exp y⌋₊ % q) *
              movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
          else 0)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  sorry

end Ostmann

end OAI
end
