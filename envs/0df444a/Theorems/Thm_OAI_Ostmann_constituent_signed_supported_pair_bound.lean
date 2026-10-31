-- Prove2me | Theorems.Thm_OAI_Ostmann_constituent_signed_supported_pair_bound
-- name    : OAI.Ostmann.constituent_signed_supported_pair_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:15.384543+00:00
-- url     : https://prove2.me/theorems/89d51aa6-570f-4d4f-8e9d-e160eb316ef0
-- title:
--   OAI.Ostmann.constituent_signed_supported_pair_bound: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.constituent_signed_supported_pair_bound` of [lean/OAI/NumberTheory/Ostmann/Construction/ConstituentSignedSupportedPair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentSignedSupportedPair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem constituent_signed_supported_pair_bound
--       (a b : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (hab : a ≠ b)
--       (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
--       (B : ℕ) (hB : 1 ≤ B) (hwords : ((expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound)).WordsBounded B) (hwordsR : ((expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound)).WordsBounded B)
--       (hD : ((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).WordsBounded B) (hD' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges)).WordsBounded B)
--       (hU : ((expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role))).WordsBounded B) (hU' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role))).WordsBounded B)
--       (hself : ((constituentMatchedGraph role size pivot n e)) a a = 0 ∧ ((constituentMatchedGraph role size pivot n e)) b b = 0) (hreverse : ((constituentMatchedGraph role size pivot n e)) b a = 0)
--       (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
--       (Q : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
--       (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
--       (hnonprincipal : ∀ q ∈ Q a, ((scheduledRetainedCharacters (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) χ n) a q) ^ ((constituentMatchedGraph role size pivot n e)) a b ≠ 1)
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
--       (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
--       (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
--       (hword : Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) + 1 ≤ B)
--       (Z : ℝ) (hZ : 0 < Z)
--       (hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
--         (scheduleFourierLeaf role ψ X lo hi) Z)
--       (δ : ℝ) (hδ : 0 ≤ δ)
--       (hnum : rangedWordTransferPairBound (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound) (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound) (((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)).map some) n Z 0)) (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges) t t' ht ht' B (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi) (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)
--         A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
--       let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
--         normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
--       let core := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P => constituentCharacterCore role size χ κ pivot n P hprime
--         childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
--       ‖∑ x : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) ⊕ (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) → P,
--         ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
--         ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
--         (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
--         (∏ h : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
--         (δ + ((SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n) *
--           (SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n)) *
--           (((((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i)))).count + ((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i)))).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
--             (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length) *
--           (α + Real.log R / V * α))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ConstituentHProductLower`, `OAI.Ostmann.CopyScheduleAtoms`, `OAI.Ostmann.CopyScheduleH`, `OAI.Ostmann.CopyScheduleRole`, `OAI.Ostmann.CopyScheduleSurvives`, `OAI.Ostmann.CopyScheduleVertex`, `OAI.Ostmann.CopyScheduleY`, `OAI.Ostmann.ExpandedScheduledVariable`, `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.InsertedConstituentVariable`, `OAI.Ostmann.NonzeroInternalFrequencies`, `OAI.Ostmann.ScheduleAtomRange`, `OAI.Ostmann.ScheduleAtomState`, `OAI.Ostmann.TopPrimeCondition`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.copyScheduleOrigin`, `OAI.Ostmann.copyScheduleRole`, `OAI.Ostmann.copyScheduleVertexFintype`, `OAI.Ostmann.normalizedFourierProfile`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.totalAtomUnitRanges`, `OAI.Ostmann.CopyScheduleRole.copiedAt`, `OAI.Ostmann.CopyScheduleRole.erasedAt`, `OAI.Ostmann.WordFourierParameters`, `OAI.Ostmann.WordFourierParameters.uniform`, `OAI.Ostmann.WordPrimeDecoration.count`, `OAI.Ostmann.WordRangeDecoration.WordsBounded`, `OAI.Ostmann.WordRangeDecoration.prependRoot` and `OAI.Ostmann.WordTransferTemplate.WordsBounded` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.retainedHWord` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.atomPairChecks`, `OAI.Ostmann.constituentCharacterCore`, `OAI.Ostmann.constituentMatchedGraph`, `OAI.Ostmann.constituentPrimePairChecks`, `OAI.Ostmann.expandedRootRanges`, `OAI.Ostmann.expandedRootTemplate`, `OAI.Ostmann.expandedSchedulePrimes`, `OAI.Ostmann.insertedConstituentPerm`, `OAI.Ostmann.insertedConstituentWord`, `OAI.Ostmann.scheduleAtomTotal`, `OAI.Ostmann.scheduleFourierLeaf` and `OAI.Ostmann.scheduledRetainedCharacters` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.originalProductRange` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.rangedWordTransferPairBound` and `OAI.Ostmann.wordTransferFullPeriod` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.eventual_selected_nonanchor_product_decay` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentSignedSupportedPair.lean (declaration OAI.Ostmann.constituent_signed_supported_pair_bound)

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
open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
variable (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

include hreal hu hκ hχ in
theorem constituent_signed_supported_pair_bound
    (a b : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : ((expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound)).WordsBounded B) (hwordsR : ((expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound)).WordsBounded B)
    (hD : ((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).WordsBounded B) (hD' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges)).WordsBounded B)
    (hU : ((expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role))).WordsBounded B) (hU' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role))).WordsBounded B)
    (hself : ((constituentMatchedGraph role size pivot n e)) a a = 0 ∧ ((constituentMatchedGraph role size pivot n e)) b b = 0) (hreverse : ((constituentMatchedGraph role size pivot n e)) b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, ((scheduledRetainedCharacters (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) χ n) a q) ^ ((constituentMatchedGraph role size pivot n e)) a b ≠ 1)
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
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hword : Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound) (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound) (((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)).map some) n Z 0)) (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges) t t' ht ht' B (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi) (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ‖∑ x : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) ⊕ (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
      (δ + ((SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n)) *
        (((((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i)))).count + ((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i)))).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length) *
        (α + Real.log R / V * α)) := by
  sorry

end
end Ostmann

end OAI
end
