-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem41
-- name    : NegativeDP.EssFinite.Supplement.theorem41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:51:51.569127+00:00
-- url     : https://prove2.me/theorems/cc241b6d-a7e3-4db6-8f91-7dd5892c8373
-- title:
--   Theorem 4.1 (D, P) — random semi-Markov and random Markov policies with the same return, for every return function
-- statement:
--   Let $\pi$ be any policy (randomized, depending on the whole history) and $p$ a probability on $S$. Then there are a random semi-Markov policy $\pi^*$ (each $\pi^*_n$ a kernel in $Q(A\mid SS)$, depending on the initial and the current state) and a random Markov policy $\pi^{**}$ (each $\pi^{**}_n\in Q(A\mid S)$) such that, for **every** return function $r$,
--
--   $$
--   I(\pi)=I(\pi^*)\quad\text{and}\quad pI(\pi)=pI(\pi^{**}).
--   $$
--
--   The policies are chosen once, before $r$. The item states this in the discounted case (every bounded Borel $r$, same $q$ and $\beta$) and in the positive bounded case (every return making the problem positive bounded, same $q$). The negative case of this theorem is the published item `NegativeDP.Stationary.theorem41`; together with this item it covers the whole source theorem.
--
--   The theorem reduces every question about returns to semi-Markov or Markov policies; it is the first step of Theorems 4.3 and 4.4.
--
--   **Formalization Note** The first conjunct is case D, with Blackwell's `Problem` and return `I`; "every return function" is every `P'` with `P'.q = P.q` and `P'.β = P.β`. The second conjunct is case P, with `Pos.Problem` and `Pos.I`; "every return function" is every positive bounded `P'` with `P'.q = P.q`. $pI$ is `∫ s, I P' π s ∂p`. Policy classes are the published `IsRandomSemiMarkov` and `IsRandomMarkov`.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.Stationary.theorem41; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - reading: for any return function r → for every problem of the same case with the same law of motion q (and, in case D, the same β); reason: r ranges over the return functions admissible in the case at hand; q and β are the fixed data of the problem
--   - encoding: pI = ∫ I dp → Bochner integral ∫ s, I s ∂p of the bounded Borel function I(π); reason: I(π) is bounded and Borel, so the Bochner integral is the integral the paper means
--   - encoding: positive bounded return I(π) in [0, R] → Pos.I = real value of the [0, ∞] sum Pos.Data.IE, bounded by R in the problem; reason: the bound makes the real value exact; no instance changes
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 876, Theorem 4.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_Stationary_Model
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)
open NegativeDP.Stationary (switchAt prefixPlan IsSemiMarkov IsMarkov IsRandomSemiMarkov IsRandomMarkov)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 4.1 (p. 876), discounted and positive bounded cases. For any policy `π` and
`p ∈ P(S)` there are a random semi-Markov `π*` and a random Markov `π**`, chosen before the
return function, with `I(π) = I(π*)` and `pI(π) = pI(π**)` for every return function `r`
(every problem of the same case with the same law of motion, and in case D the same `β`).
The negative case is the published `NegativeDP.Stationary.theorem41`. -/
theorem theorem41 :
    (∀ (P : Problem S A) (π : Plan (S := S) (A := A)) (p : Measure S), IsProbabilityMeasure p →
      ∃ π₁ π₂ : Plan (S := S) (A := A), IsRandomSemiMarkov π₁ ∧ IsRandomMarkov π₂ ∧
        ∀ P' : Problem S A, P'.q = P.q → P'.β = P.β →
          (∀ s, I P' π s = I P' π₁ s) ∧ ∫ s, I P' π s ∂p = ∫ s, I P' π₂ s ∂p) ∧
    (∀ (P : Pos.Problem S A) (π : Plan (S := S) (A := A)) (p : Measure S), IsProbabilityMeasure p →
      ∃ π₁ π₂ : Plan (S := S) (A := A), IsRandomSemiMarkov π₁ ∧ IsRandomMarkov π₂ ∧
        ∀ P' : Pos.Problem S A, P'.q = P.q →
          (∀ s, Pos.I P' π s = Pos.I P' π₁ s) ∧ ∫ s, Pos.I P' π s ∂p = ∫ s, Pos.I P' π₂ s ∂p) := by sorry

end NegativeDP.EssFinite.Supplement
