-- Prove2me | Theorems.Thm_OAI_Ostmann_eventual_constituent_final_pair_decay
-- name    : OAI.Ostmann.eventual_constituent_final_pair_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:48.075357+00:00
-- url     : https://prove2.me/theorems/920b8ea8-c471-4598-99c9-9fcf221c54c7
-- title:
--   OAI.Ostmann.eventual_constituent_final_pair_decay: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.eventual_constituent_final_pair_decay` of [lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairDecay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairDecay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform`):
--
--   ```lean
--   theorem eventual_constituent_final_pair_decay
--       (n : ℕ) (a₀ b₀ d₀ C S H z α₀ β γ c : ℝ)
--       (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) (hS : 1 ≤ S)
--       (hH : 0 ≤ H) (hz : 0 ≤ z)
--       (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (I : Type u) [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
--         (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
--         (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
--         (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
--         (e : Equiv.Perm (SurvivingConstituent role size n))
--         (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
--         (childBound pivotBound : ℕ → ℕ)
--         (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
--         (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
--         (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
--         (_hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
--       let K := SurvivingConstituent role size n
--       let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
--       let W := primeWordEmbedding (scheduleConstituentWord role size n)
--       let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
--       let G := graphDifference (scheduledSurvivorGraph ρ pivot n)
--         (transportGraph e (scheduledSurvivorGraph ρ pivot n))
--       let Tpl := expandedRootTemplate role n W childBound pivotBound
--       let Tpl' := expandedRootTemplate role n W' childBound pivotBound
--       let D := expandedRootRanges role n W ranges
--       let D' := expandedRootRanges role n W' ranges
--       let U := expandedRootRanges role n W (totalAtomUnitRanges role)
--       let U' := expandedRootRanges role n W' (totalAtomUnitRanges role)
--       let Pr := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
--       let Pr' := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
--       let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
--       ∀
--       (a b : K) (_hab : a ≠ b)
--       (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
--       (_ht' : NonzeroInternalFrequencies n t') (_hroot : frequencyRoot n t = frequencyRoot n t')
--       (B : ℕ) (_hB : 1 ≤ B) (_hwords : (Tpl).WordsBounded B) (_hwords' : (Tpl').WordsBounded B)
--       (_hD : (D).WordsBounded B) (_hD' : (D').WordsBounded B)
--       (_hU : (U).WordsBounded B) (_hU' : (U').WordsBounded B) (_hreverse : G b a = 0)
--       (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
--       (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
--       (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
--       (_hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
--       (A E : ℕ) (_hA : 0 < A)
--       (_hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
--       (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
--       (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
--       (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
--       (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
--       (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
--       (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R)
--       (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
--       (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
--       (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
--       (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L)
--       (Vfreq : ℕ) (_hBlinear : (B : ℝ) ≤ b₀ * (1 + M))
--       (_hDcount : (((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)).count : ℝ) ≤ d₀ * (1 + M))
--       (_hD'count : ((D').count : ℝ) ≤ d₀ * (1 + M))
--       (_hVfreq : (Vfreq : ℝ) ≤ Real.exp (C * (1 + M)))
--       (_hfv : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ Vfreq)
--       (_hfv' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ Vfreq)
--       (_hs₀ : SchwartzMap.seminorm ℝ 0 0 (FP).profile ≤ S)
--       (_hs₁ : SchwartzMap.seminorm ℝ 0 1 (FP).profile ≤ S)
--       (_hwidth : ∀ i, (FP).upper i - (FP).lower i ≤ Real.exp (C * (1 + M)))
--       (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
--       (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
--       (_hshort : Real.exp (c * Real.exp (α₀ * L)) ≤ lower)
--       (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
--       (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
--       (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α₀ * L)) ≤ (p : ℝ))
--       (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
--       (_hprimecount : (((Pr).count + (Pr').count : ℕ) : ℝ) ≤ a₀ * (1 + M))
--       (_hcheckcount : ((constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
--         a₀ * (1 + M) ^ 2)
--       (center : ∀ p : ℕ, ZMod p),
--       ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
--         (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
--           (scheduleFourierLeaf role ψ X lo hi) center t q *
--         conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
--           (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
--         Real.exp (-(c / 32) * Real.exp (α₀ * L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.CopyScheduleAtoms`, `OAI.Ostmann.CopyScheduleRole`, `OAI.Ostmann.CopyScheduleSurvives`, `OAI.Ostmann.CopyScheduleVertex`, `OAI.Ostmann.ExpandedScheduledVariable`, `OAI.Ostmann.FrequencyTree`, `OAI.Ostmann.NonzeroInternalFrequencies`, `OAI.Ostmann.ScheduleAtomRange`, `OAI.Ostmann.SurvivingConstituent`, `OAI.Ostmann.TopPrimeCondition`, `OAI.Ostmann.WordFourierParameters`, `OAI.Ostmann.WordPrimeDecoration`, `OAI.Ostmann.WordRangeDecoration`, `OAI.Ostmann.WordTransferTemplate`, `OAI.Ostmann.allFrequencyList`, `OAI.Ostmann.copyScheduleOrigin`, `OAI.Ostmann.copyScheduleVertexFintype`, `OAI.Ostmann.frequencyRoot`, `OAI.Ostmann.primeSubsetPrior`, `OAI.Ostmann.totalAtomUnitRanges`, `OAI.Ostmann.WordFourierParameters.uniform`, `OAI.Ostmann.WordPrimeDecoration.count`, `OAI.Ostmann.WordRangeDecoration.WordsBounded`, `OAI.Ostmann.WordRangeDecoration.count`, `OAI.Ostmann.WordRangeDecoration.prependRoot` and `OAI.Ostmann.WordTransferTemplate.WordsBounded` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.graphDifference`, `OAI.Ostmann.primeWordEmbedding` and `OAI.Ostmann.transportGraph` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.atomPairChecks`, `OAI.Ostmann.constituentPrimePairChecks`, `OAI.Ostmann.constituentPrimeTerm`, `OAI.Ostmann.expandedRootRanges`, `OAI.Ostmann.expandedRootTemplate`, `OAI.Ostmann.expandedSchedulePrimes`, `OAI.Ostmann.scheduleConstituentWord` and `OAI.Ostmann.scheduleFourierLeaf` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.originalProductRange` and `OAI.Ostmann.scheduledSurvivorGraph` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.wordTransferFullPeriod` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.eventual_character_final_contradiction` and `OAI_Ostmann_selected_natural_final_contradiction` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Construction/ConstituentFinalPairDecay.lean (declaration OAI.Ostmann.eventual_constituent_final_pair_decay)

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
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_constituent_final_pair_decay
    (n : ℕ) (a₀ b₀ d₀ C S H z α₀ β γ c : ℝ)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) (hS : 1 ≤ S)
    (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type u) [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (SurvivingConstituent role size n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := SurvivingConstituent role size n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let W := primeWordEmbedding (scheduleConstituentWord role size n)
    let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
    let G := graphDifference (scheduledSurvivorGraph ρ pivot n)
      (transportGraph e (scheduledSurvivorGraph ρ pivot n))
    let Tpl := expandedRootTemplate role n W childBound pivotBound
    let Tpl' := expandedRootTemplate role n W' childBound pivotBound
    let D := expandedRootRanges role n W ranges
    let D' := expandedRootRanges role n W' ranges
    let U := expandedRootRanges role n W (totalAtomUnitRanges role)
    let U' := expandedRootRanges role n W' (totalAtomUnitRanges role)
    let Pr := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
    let Pr' := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀
    (a b : K) (_hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
    (_ht' : NonzeroInternalFrequencies n t') (_hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (_hB : 1 ≤ B) (_hwords : (Tpl).WordsBounded B) (_hwords' : (Tpl').WordsBounded B)
    (_hD : (D).WordsBounded B) (_hD' : (D').WordsBounded B)
    (_hU : (U).WordsBounded B) (_hU' : (U').WordsBounded B) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L)
    (Vfreq : ℕ) (_hBlinear : (B : ℝ) ≤ b₀ * (1 + M))
    (_hDcount : (((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)).count : ℝ) ≤ d₀ * (1 + M))
    (_hD'count : ((D').count : ℝ) ≤ d₀ * (1 + M))
    (_hVfreq : (Vfreq : ℝ) ≤ Real.exp (C * (1 + M)))
    (_hfv : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ Vfreq)
    (_hfv' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ Vfreq)
    (_hs₀ : SchwartzMap.seminorm ℝ 0 0 (FP).profile ≤ S)
    (_hs₁ : SchwartzMap.seminorm ℝ 0 1 (FP).profile ≤ S)
    (_hwidth : ∀ i, (FP).upper i - (FP).lower i ≤ Real.exp (C * (1 + M)))
    (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
    (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
    (_hshort : Real.exp (c * Real.exp (α₀ * L)) ≤ lower)
    (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
    (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
    (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α₀ * L)) ≤ (p : ℝ))
    (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
    (_hprimecount : (((Pr).count + (Pr').count : ℕ) : ℝ) ≤ a₀ * (1 + M))
    (_hcheckcount : ((constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      a₀ * (1 + M) ^ 2)
    (center : ∀ p : ℕ, ZMod p),
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
      Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
  sorry

end Ostmann

end OAI
end
