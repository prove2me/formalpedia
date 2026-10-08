-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_actual_affine_word_comparison
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:31.141146+00:00
-- url     : https://prove2.me/theorems/1de13359-a5cf-4432-be4c-93a0433430a2
-- title:
--   Under Braverman's theorem, affine progressions equidistribute the masked signed walk products of the prohibited-prime model
-- statement:
--   Assume `BravermanDepth22Input` (Braverman's theorem for depth-22 circuits: there are $K,C>0$ such that for every AC⁰ circuit $c$ of depth at most $22$, every $\varepsilon\in(0,1/2]$, and every $t\ge K\log(\mathrm{size}(c)/\varepsilon)^C$, every nonnegative density $g$ on the Boolean cube with mean $1$ that is $t$-wise uniform (`TWiseUniformDensity g t`) satisfies $|\mathbb E[g\,\mathbf 1_c]-\mathbb E[\mathbf 1_c]|\le\varepsilon$).
--
--   Then there is a natural number $A\ge1000$ such that for all sufficiently large real $L$ the following holds. Let $h,J,M,R,s,B$ be naturals and let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`: disjoint finite sets $P,Q$ of primes, with $P$ avoiding the prime factors of $h$, and a finite set of pairs $(d,q)$ of squarefree numbers with $d$ having exactly $J$ prime factors, all in $P$, and $q$ at most $M$ prime factors, in $Q$; see the bundle for the complete list of fields). Suppose every prime of $P\cup Q$ is at most $B$, $P\cup Q\ne\varnothing$, $B\le e^L$, $s\le L$, $J+M\le L^2$, the number of pairs is at most $e^{101L}$, $0<R$, $R+1\le4L$ and $RJ\le L^2$. Let $Q'\subseteq$ `retainedPrimeDivisors data.Q`, let $P_1,\dots,P_J$ be pairwise disjoint finite sets of primes, let $w$ be a column prime assignment (`ColumnPrimeAssignment J R P`), `forward` a choice of directions $\{1,\dots,R\}\to\{\text{true},\text{false}\}$ and `padding` naturals indexed by $\{1,\dots,R\}$, each with at most $100\log L$ distinct prime factors. Let `label` assign to each $(i,j)$ an element of $P\cup Q$ equal to $w_j(i)$, and suppose the walk word `columnTupleWord w forward padding` has zero displacement relative to $h$ (`wordDisplacement`). Then for every predicate `eligible`, every real $K$ and all naturals $a,l,N$ with $l$ coprime to every prime of $P\cup Q$ and $N\ge\exp(L^A/2)$, with the weight `maskedSignedIntegerWeight …` written out in the statement,
--
--   $$\Big|\frac1N\sum_{x<N}\Pi(a+lx)-\mathbb E_{r}\,\Pi(\mathrm{origin}(r))\Big|\le e^{-L^9},$$
--
--   where $\Pi(y)$ is the scalar walk product `scalarWalkProduct h weight y (columnTupleWord w forward padding)`, and the expectation is over the family's residue law `data.residueLaw B hB` with origins `data.residueOrigin r`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_actual_affine_word_comparison`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_actual_affine_word_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M R s B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → ((J + M : ℕ) : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      0 < R → ((R + 1 : ℕ) : ℝ) ≤ 4 * L → ((R * J : ℕ) : ℝ) ≤ L ^ 2 →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (P : Fin J → Finset ℕ)
        (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ i, ((padding i).primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (label : Fin R × Fin J → ↥(data.P ∪ data.Q)),
      (∀ i j, (label (i, j)).val = (w j i).val) →
      wordDisplacement h (columnTupleWord w forward padding) = 0 →
      ∀ (eligible : ℕ → ℕ → Prop) (K : ℝ) (a l N : ℕ),
      (∀ p ∈ data.P ∪ data.Q, l.Coprime p) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient eligible
        (actualPaddingVertex data.Q) (fun d => centeredTuple d.primeFactors) L K
        (fun _ => actualPaddingDegreeCut data.Q L) h
        (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z)
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward padding)) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward padding))| ≤ Real.exp (-(L ^ 9)) := by
  sorry

end OAI.TwoPointCorrelations
