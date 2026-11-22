-- Prove2me | Theorems.Thm_HardyLittlewoodMaximal_vitali_covering_lemma_euclidean
-- name    : HardyLittlewoodMaximal.vitali_covering_lemma_euclidean
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:48:53.130594+00:00
-- url     : https://prove2.me/theorems/10e746e6-1628-4836-99f4-63f713114492
-- title:
--   Vitali covering lemma in $\mathbb R^d$: finitely many disjoint balls of a family $\mathcal C$ have total measure $>3^{-d}c$, for every $c<m(\bigcup\mathcal C)$
-- statement:
--   **Vitali covering lemma (finite form, with the constant $3^{-d}$).** Let $d\ge 0$ be an integer, let $m$ denote Lebesgue measure on $\mathbb R^d$, and let $\mathcal C$ be an arbitrary collection of open balls $B(x,r)=\{y\in\mathbb R^d:\ |y-x|<r\}$, $r>0$, for the Euclidean norm. Put
--   $$U=\bigcup_{B\in\mathcal C}B .$$
--   Then for every $c<m(U)$ there exist finitely many pairwise disjoint balls $B_1,\dots,B_k\in\mathcal C$ such that
--   $$\sum_{j=1}^{k}m(B_j)\;>\;3^{-d}\,c .$$
--
--   No assumption is made on the family: it may be uncountable, the radii may be unbounded, and $m(U)$ may be infinite.
--
--   This is the covering lemma on which the weak type $(1,1)$ inequality for the Hardy–Littlewood maximal function rests, and it is the reason for the constant $3^d$ there. The source refers to it in Remark A.5.1.2 for exactly this purpose, and Theorem A.5.3.1 of the source is its analogue for translates of a D-sequence in a locally compact abelian group.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with its Lebesgue measure `volume`, and the family is a set `𝒞` of subsets each of which is a `Metric.ball x r` with `0 < r`. The number $c$ ranges over $[0,\infty]$, so that `c < volume (⋃₀ 𝒞)` forces $c<\infty$. The chosen balls form a `Finset` contained in `𝒞` whose members are pairwise disjoint, and the conclusion $\sum_j m(B_j)>3^{-d}c$ is written `c / 3 ^ d < ∑ B ∈ s, volume B`. The source cites the lemma without reproducing it; the statement is the standard one.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 568, Remark A.5.1.2 (and p. 579, Remark A.5.3.2); classical reference: G. B. Folland, Real Analysis. Modern Techniques and Their Applications, Second Edition, John Wiley and Sons, 1999, Lemma 3.15 (see also E. M. Stein and R. Shakarchi, Real Analysis. Measure Theory, Integration and Hilbert Spaces, Princeton Lectures in Analysis III, 2005, Ch. 3, §1, Lemma 1.2, p. 102), as cited by the paper

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace HardyLittlewoodMaximal

theorem vitali_covering_lemma_euclidean (d : ℕ) (𝒞 : Set (Set (EuclideanSpace ℝ (Fin d))))
    (h𝒞 : ∀ B ∈ 𝒞, ∃ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r ∧ B = Metric.ball x r)
    (c : ℝ≥0∞) (hc : c < volume (⋃₀ 𝒞)) :
    ∃ s : Finset (Set (EuclideanSpace ℝ (Fin d))),
      (↑s : Set (Set (EuclideanSpace ℝ (Fin d)))) ⊆ 𝒞 ∧
      (↑s : Set (Set (EuclideanSpace ℝ (Fin d)))).PairwiseDisjoint id ∧
      c / 3 ^ d < ∑ B ∈ s, volume B := by sorry

end HardyLittlewoodMaximal
