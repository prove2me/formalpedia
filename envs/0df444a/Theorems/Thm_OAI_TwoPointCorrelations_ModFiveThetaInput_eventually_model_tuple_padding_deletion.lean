-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_model_tuple_padding_deletion
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_model_tuple_padding_deletion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:24.429779+00:00
-- url     : https://prove2.me/theorems/24aa013f-5764-475e-b40d-64dc75a3659b
-- title:
--   Under the mod-5 prime number theorem, the model cost of deleting rejected paddings
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals. Then there is $C>0$ such that for all sufficiently large $L$: for every prohibited prime family `data` (`ProhibitedPrimeFamily h J M`) with data.Q = `paddingPrimeSupply E L` and all primes at most $B$; pairwise disjoint sets of primes $P_1,\dots,P_J$ whose union is data.P; $D\subseteq$ `primeTupleDivisors P`; $Q'\subseteq$ `retainedPrimeDivisors data.Q`; a finite set of bins, $\eta\in(0,1]$, $K>0$, $c:\mathbb N\to\mathbb R$ and an integer site:
--
--   $$\frac{\mathbb E_x\sum_{d\in D}\texttt{positivePrimeWeight}(d,y_x)\cdot\texttt{paddingRejectedMass}(\mathrm{data}.Q,Q',\mathrm{bins},\eta,c(d),L,K,y_x)}{\texttt{paddingTiltNormalizer}(\mathrm{data}.Q)}\le2^J\Big(\prod_j\sum_{p\in P_j}\frac1p\Big)\Big(\frac CK+L^{-100}\Big),$$
--
--   with $y_x$ = `data.residueOrigin x + site`, the expectation over `data.residueLaw B hB`, and the weight taken at the prime factors of $d$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_model_tuple_padding_deletion`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_model_tuple_padding_deletion
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K → ∀ site : ℤ,
      (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
