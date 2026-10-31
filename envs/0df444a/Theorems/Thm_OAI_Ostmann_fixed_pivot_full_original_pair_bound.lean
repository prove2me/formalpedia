-- Prove2me | Theorems.Thm_OAI_Ostmann_fixed_pivot_full_original_pair_bound
-- name    : OAI.Ostmann.fixed_pivot_full_original_pair_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:25:19.134511+00:00
-- url     : https://prove2.me/theorems/7721b5a1-acd0-4e1e-9d50-725cb033b4d8
-- title:
--   OAI.Ostmann.fixed_pivot_full_original_pair_bound: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.fixed_pivot_full_original_pair_bound` of [lean/OAI/NumberTheory/Ostmann/Construction/FixedPivotFullPair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/FixedPivotFullPair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped BigOperators ComplexConjugate Classical SchwartzMap`):
--
--   ```lean
--   theorem fixed_pivot_full_original_pair_bound {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
--       (a b : K) (hab : a ≠ b)
--       (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
--       (C C' : WordPrimeDecoration (Option (K)) n)
--       (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
--       (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
--       (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
--       (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
--       (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
--       (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
--       (f f' : WordFourierParameters n)
--       (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
--       (graph : Option (K) → Option (K) → ℤ)
--       (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
--       (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
--       (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
--       (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
--       (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
--       (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
--       (A E : ℕ) (hA : 0 < A)
--       (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
--       (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
--       (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
--       (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
--       (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
--       (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
--       (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
--       (M : ℕ) (hM : (M : ℝ) ≤ R)
--       (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
--       (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
--       (checks : J → TopPrimeCondition (K))
--       (hchecks : ∀ j, (checks j).Bounded R)
--       (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
--       (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
--       (δ : ℝ) (hδ : 0 ≤ δ)
--       (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
--         A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
--       ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
--         (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
--           finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
--           (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
--             conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)‖ ≤
--         δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
--           (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
--           (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
--           (α + Real.log R / V * α)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ExpandedScheduledVariable`, `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.NonzeroInternalFrequencies`, `OAI.Ostmann.TopPrimeCondition`, `OAI.Ostmann.WordFourierParameters`, `OAI.Ostmann.WordPrimeDecoration`, `OAI.Ostmann.WordRangeDecoration`, `OAI.Ostmann.WordTransferTemplate`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.TopPrimeCondition.Bounded`, `OAI.Ostmann.TopPrimeCondition.Holds`, `OAI.Ostmann.WordFourierParameters.primeUnitRangedCoefficient`, `OAI.Ostmann.WordPrimeDecoration.Coordinates`, `OAI.Ostmann.WordPrimeDecoration.count`, `OAI.Ostmann.WordRangeDecoration.WordsBounded` and `OAI.Ostmann.WordTransferTemplate.WordsBounded` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.dirichletGraphEdge`, `OAI.Ostmann.finiteEdgeWeight` and `OAI.Ostmann.fixedPivotPrimeValues` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.rangedWordTransferPairBound` and `OAI.Ostmann.wordTransferFullPeriod` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.constituent_final_pair_bound` and `OAI.Ostmann.constituent_signed_supported_pair_bound` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/FixedPivotFullPair.lean (declaration OAI.Ostmann.fixed_pivot_full_original_pair_bound)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_full_original_pair_bound {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Option (K) → Option (K) → ℤ)
    (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (checks : J → TopPrimeCondition (K))
    (hchecks : ∀ j, (checks j).Bounded R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
        finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
        (α + Real.log R / V * α) := by
  sorry

end Ostmann

end OAI
end
