-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_shifted_actual_prohibited_deletion_uniform
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:43.764547+00:00
-- url     : https://prove2.me/theorems/ac7a2750-b39c-4a1f-bb8f-375e68bd7908
-- title:
--   Under Braverman's theorem and the mod-5 prime number theorem, shifted prohibited rows have small average
-- statement:
--   Assume `BravermanDepth22Input` and `ModFiveThetaInput` (the bundle's Braverman theorem for depth-22 circuits and the prime number theorem with de la Vallée Poussin error for the two prime classes modulo 5). Then there is a natural $A\ge1000$ such that for every finite $E\subseteq\mathbb N$ and reals $W\ge10$, $C\ge0$, for all sufficiently large $L$: let $h,M,B,s,\mathrm{cap}$ be naturals and `data` a prohibited prime family (`ProhibitedPrimeFamily h J M` with $J$ = `primeSupplyCount W L`) whose $P$ is `centeredPrimePool E (L^{199/200}) W J` and whose $Q$ is `paddingPrimeSupply E L`, with all its primes at most $B\le e^L$, $P\cup Q\ne\varnothing$, $s\le L$, $\mathrm{cap}\le L^2$, at most $e^{101L}$ pairs, each pair $(d,q)$ having $qd$ with at most cap prime factors, the deleted event `data.deletedEvent s B` of probability at most $\exp(-\tfrac12L^{199/200})$ under `data.residueLaw`, and $J\le L^2$. Let $D$ be a set of prime-tuple divisors of the centered bands, `padding` assign to each $d\in D$ a set of retained divisors of $Q$ with at most $100\log L$ prime factors each and with $(d,q)$ a pair of the family, $0\le T\le\exp(C\log L)$, a site function, and $a,N$ with $N\ge\exp(L^A/2)$. Then
--
--   $$T\cdot\frac1N\sum_{x<N}\texttt{shiftedProhibitedRow}(\mathrm{data},s,D,\mathrm{padding},\mathrm{site},a+x)\le e^{-L^{9/10}}+T\cdot\#\mathrm{pairs}\cdot e^{-L^9}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_shifted_actual_prohibited_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (E : Finset ℕ) (W C : ℝ),
      10 ≤ W → 0 ≤ C → ∀ᶠ L : ℝ in atTop,
      ∀ (h M B s cap : ℕ) (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      (primeSupplyCount W L : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      (∀ d ∈ D, ∀ q ∈ padding d, (d, q) ∈ data.pairs) →
      ∀ (T : ℝ), 0 ≤ T → T ≤ Real.exp (C * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      T * uniformAverage (fun x : Fin N =>
        shiftedProhibitedRow data s D padding site (a + x.val)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) +
            T * data.pairs.card * Real.exp (-(L ^ 9)) := by
  sorry

end OAI.TwoPointCorrelations
