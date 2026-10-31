-- Prove2me | Theorems.Thm_OAI_Ostmann_constituent_final_pair_bound
-- name    : OAI.Ostmann.constituent_final_pair_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:20:30.019585+00:00
-- url     : https://prove2.me/theorems/401ee36e-1dd2-43fb-88b5-1ecea85914b1
-- title:
--   OAI.Ostmann.constituent_final_pair_bound: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.constituent_final_pair_bound` of [lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem constituent_final_pair_bound
--       (a b : K) (hab : a ≠ b)
--       (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
--       (ht' : NonzeroInternalFrequencies n t') (hroot : frequencyRoot n t = frequencyRoot n t')
--       (B : ℕ) (hB : 1 ≤ B) (hwords : (Tpl).WordsBounded B) (hwords' : (Tpl').WordsBounded B)
--       (hD : (D).WordsBounded B) (hD' : (D').WordsBounded B)
--       (hU : (U).WordsBounded B) (hU' : (U').WordsBounded B) (hreverse : G b a = 0)
--       (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
--       (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
--       (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
--       (hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
--       (A E : ℕ) (hA : 0 < A)
--       (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
--       (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
--       (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
--       (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
--       (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
--       (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
--       (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
--       (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
--       (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
--       (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
--       (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
--       (δ : ℝ) (hδ : 0 ≤ δ)
--       (hnum : rangedWordTransferPairBound Tpl Tpl'
--         ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D' t t' ht ht' B FP FP
--         A E (Q b) (Q a) lower Bq ≤ δ ^ 2)
--       (center : ∀ p : ℕ, ZMod p) :
--       ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
--         (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
--           (scheduleFourierLeaf role ψ X lo hi) center t q *
--         conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
--           (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
--       δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
--         (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
--         ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
--           (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length) *
--         (α + Real.log R / V * α)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CopyScheduleAtoms`, `OAI.Ostmann.CopyScheduleRole`, `OAI.Ostmann.CopyScheduleSurvives`, `OAI.Ostmann.CopyScheduleVertex`, `OAI.Ostmann.ExpandedScheduledVariable`, `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.NonzeroInternalFrequencies`, `OAI.Ostmann.ScheduleAtomRange`, `OAI.Ostmann.SurvivingConstituent`, `OAI.Ostmann.TopPrimeCondition`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.copyScheduleOrigin`, `OAI.Ostmann.copyScheduleVertexFintype`, `OAI.Ostmann.frequencyRoot`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.totalAtomUnitRanges`, `OAI.Ostmann.WordFourierParameters`, `OAI.Ostmann.WordFourierParameters.uniform`, `OAI.Ostmann.WordPrimeDecoration.count`, `OAI.Ostmann.WordRangeDecoration.WordsBounded`, `OAI.Ostmann.WordRangeDecoration.prependRoot` and `OAI.Ostmann.WordTransferTemplate.WordsBounded` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.graphDifference`, `OAI.Ostmann.primeWordEmbedding` and `OAI.Ostmann.transportGraph` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.atomPairChecks`, `OAI.Ostmann.constituentPrimePairChecks`, `OAI.Ostmann.constituentPrimeTerm`, `OAI.Ostmann.expandedRootRanges`, `OAI.Ostmann.expandedRootTemplate`, `OAI.Ostmann.expandedSchedulePrimes`, `OAI.Ostmann.scheduleConstituentWord` and `OAI.Ostmann.scheduleFourierLeaf` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.originalProductRange` and `OAI.Ostmann.scheduledSurvivorGraph` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.rangedWordTransferPairBound` and `OAI.Ostmann.wordTransferFullPeriod` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_constituent_final_pair_decay` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairBound.lean (declaration OAI.Ostmann.constituent_final_pair_bound)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (SurvivingConstituent role size n))
variable (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
local notation "K" => SurvivingConstituent role size n
local notation "ρ" => (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
local notation "W" => primeWordEmbedding (scheduleConstituentWord role size n)
local notation "W'" => primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
local notation "G" => graphDifference (scheduledSurvivorGraph ρ pivot n)
  (transportGraph e (scheduledSurvivorGraph ρ pivot n))
local notation "Tpl" => expandedRootTemplate role n W childBound pivotBound
local notation "Tpl'" => expandedRootTemplate role n W' childBound pivotBound
local notation "D" => expandedRootRanges role n W ranges
local notation "D'" => expandedRootRanges role n W' ranges
local notation "U" => expandedRootRanges role n W (totalAtomUnitRanges role)
local notation "U'" => expandedRootRanges role n W' (totalAtomUnitRanges role)
local notation "Pr" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
local notation "Pr'" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

include hκ hχ hreal hu in
theorem constituent_final_pair_bound
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t') (hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : (Tpl).WordsBounded B) (hwords' : (Tpl').WordsBounded B)
    (hD : (D).WordsBounded B) (hD' : (D').WordsBounded B)
    (hU : (U).WordsBounded B) (hU' : (U').WordsBounded B) (hreverse : G b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound Tpl Tpl'
      ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D' t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2)
    (center : ∀ p : ℕ, ZMod p) :
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
    δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
      (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
      ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length) *
      (α + Real.log R / V * α) := by
  sorry

end
end Ostmann

end OAI
end
