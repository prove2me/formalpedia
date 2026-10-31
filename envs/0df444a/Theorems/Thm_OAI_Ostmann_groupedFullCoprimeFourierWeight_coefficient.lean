-- Prove2me | Theorems.Thm_OAI_Ostmann_groupedFullCoprimeFourierWeight_coefficient
-- name    : OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:09:04.401609+00:00
-- url     : https://prove2.me/theorems/ebb96739-1559-4533-9528-d4d5ba6ceaa1
-- title:
--   OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient` of [lean/OAI/NumberTheory/Ostmann/Construction/GroupedFullCoprime.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/GroupedFullCoprime.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical SchwartzMap FourierTransform ComplexConjugate`):
--
--   ```lean
--   theorem groupedFullCoprimeFourierWeight_coefficient {I V : Type*} [Fintype I]
--       (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
--       (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
--       (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
--       (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
--       (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ)
--       (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
--       groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
--         if ∀ c ∈ atomPairChecks words, c.Holds x then
--           (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
--             (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
--             (expandedRootRanges role n words (totalAtomUnitRanges role))
--             (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
--             t ht x
--         else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CopyScheduleAtoms`, `OAI.Ostmann.CopyScheduleRole`, `OAI.Ostmann.CopyScheduleSurvives`, `OAI.Ostmann.CopyScheduleVertex`, `OAI.Ostmann.ExpandedScheduledVariable`, `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.NonzeroInternalFrequencies`, `OAI.Ostmann.ScheduleAtomRange`, `OAI.Ostmann.TopPrimeCondition`, `OAI.Ostmann.copyScheduleVertexFintype`, `OAI.Ostmann.totalAtomUnitRanges`, `OAI.Ostmann.TopPrimeCondition.Holds`, `OAI.Ostmann.WordFourierParameters.primeUnitRangedCoefficient` and `OAI.Ostmann.WordFourierParameters.uniform` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.atomPairChecks`, `OAI.Ostmann.expandedRootRanges`, `OAI.Ostmann.expandedRootTemplate`, `OAI.Ostmann.expandedSchedulePrimes` and `OAI.Ostmann.groupedFullCoprimeFourierWeight` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.constituent_final_pair_bound` and `OAI.Ostmann.constituent_signed_supported_pair_bound` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/GroupedFullCoprime.lean (declaration OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient)

import Mathlib
import Definitions.Def_OAIQ095D004

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem groupedFullCoprimeFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      if ∀ c ∈ atomPairChecks words, c.Holds x then
        (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
          (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
          (expandedRootRanges role n words (totalAtomUnitRanges role))
          (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
          t ht x
      else 0 := by
  sorry

end Ostmann

end OAI
end
