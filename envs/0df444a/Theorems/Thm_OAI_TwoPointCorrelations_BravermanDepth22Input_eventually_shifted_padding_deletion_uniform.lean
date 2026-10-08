-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_shifted_padding_deletion_uniform
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_padding_deletion_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:50.73331+00:00
-- url     : https://prove2.me/theorems/81a4ff94-18da-4c78-a456-5819a2c8d83e
-- title:
--   Under Braverman's theorem and the mod-5 prime number theorem, the shifted padding-rejection atoms are small on average
-- statement:
--   Assume `BravermanDepth22Input` and `ModFiveThetaInput`. Then there is a natural $A\ge1000$ such that for every finite $E\subseteq\mathbb N$ there is $C>0$ such that for all sufficiently large $L$: let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with $Q$ = `paddingPrimeSupply E L`, all its primes at most $B\le e^L$, $P\cup Q\ne\varnothing$; let $P_1,\dots,P_J$ be pairwise disjoint sets of primes whose union (`primeTuplePool`) is the family's $P$, with $J\le L^2$; let $D$ be a set of divisors from `primeTupleDivisors P`, $Q'$ a set of retained divisors of the family's $Q$ each with at most $100\log L$ prime factors; let bins $\subseteq\mathbb Z$ be finite, $\eta\in(0,1]$, $K>0$, $c:\mathbb N\to\mathbb R$, a site function and $a,N$ with $N_j\ge\exp(L^A/2)$ on the bins. Then
--
--   $$\frac{\sum_{j}\sum_{d\in D}\sum_{q\in Q'}\frac1{N_j}\sum_{x<N_j}\texttt{paddingRejectionAtom}(\dots,a_j+x+\mathrm{site}(j,d,q))}{\texttt{paddingTiltNormalizer}(Q)}\le2^J\Big(\prod_j\texttt{primeHarmonicMass}(P_j)\Big)\Big(\frac CK+L^{-100}\Big)+\frac{2\,\#\mathrm{bins}\,\#D\,\#Q'\,e^{-L^9}}{\texttt{paddingTiltNormalizer}(Q)}.$$
--
--   The atom is `paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q`, as defined in the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_shifted_padding_deletion_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_shifted_padding_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ E : Finset ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) / paddingTiltNormalizer data.Q ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) +
          (2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9))) /
            paddingTiltNormalizer data.Q := by
  sorry

end OAI.TwoPointCorrelations
