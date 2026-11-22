-- Prove2me | Theorems.Thm_HardyLittlewoodMaximal_vitali_covering_lemma_finite_euclidean
-- name    : HardyLittlewoodMaximal.vitali_covering_lemma_finite_euclidean
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:13.41511+00:00
-- url     : https://prove2.me/theorems/3cf33b74-99a3-4573-80e3-bab5bbfb28b2
-- title:
--   Vitali covering lemma for finitely many open balls in $\mathbb R^d$: a disjoint subcollection with $m(\bigcup_{\ell}B_\ell)\le 3^d\sum_j m(B_{i_j})$
-- statement:
--   **Vitali covering lemma for a finite collection of balls.** Let $d\ge0$ be an integer, let $m$ denote Lebesgue measure on $\mathbb R^d$, and let $\mathcal B=\{B_1,\dots,B_N\}$ be a finite collection of open balls $B(x,r)=\{y\in\mathbb R^d:\ |y-x|<r\}$, $r>0$, for the Euclidean norm. Then there exists a subcollection $B_{i_1},\dots,B_{i_k}$ of $\mathcal B$ consisting of pairwise disjoint balls such that
--   $$m\Big(\bigcup_{\ell=1}^{N}B_\ell\Big)\;\le\;3^d\sum_{j=1}^{k}m(B_{i_j}).$$
--
--   This is the covering lemma behind the weak type $(1,1)$ inequality for the Hardy–Littlewood maximal function on $\mathbb R^d$ with the constant $3^d$; the source refers to it in Remark A.5.1.2 for exactly this purpose, and Theorem A.5.3.1 of the source is its analogue for translates of a D-sequence in a locally compact abelian group.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with its Lebesgue measure `volume`. The collection is a `Finset` `𝒞` of subsets each of which is a `Metric.ball x r` with `0 < r`; the subcollection is a `Finset` `s ⊆ 𝒞` whose members are pairwise disjoint, and the union is `⋃₀ ↑𝒞`. For the empty collection both sides are $0$. The source cites the lemma without reproducing it; the statement is the standard one for finite collections. The platform statement `HardyLittlewoodMaximal.vitali_covering_lemma_euclidean` is the companion form for arbitrary families of balls (with $c<m(\bigcup\mathcal C)$ and a strict inequality).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 568, Remark A.5.1.2; classical reference: E. M. Stein and R. Shakarchi, Real Analysis. Measure Theory, Integration and Hilbert Spaces, Princeton Lectures in Analysis III, 2005, Ch. 3, §1, Lemma 1.2, p. 102 (as cited by the paper)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace HardyLittlewoodMaximal

theorem vitali_covering_lemma_finite_euclidean (d : ℕ)
    (𝒞 : Finset (Set (EuclideanSpace ℝ (Fin d))))
    (h𝒞 : ∀ B ∈ 𝒞, ∃ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r ∧ B = Metric.ball x r) :
    ∃ s : Finset (Set (EuclideanSpace ℝ (Fin d))), s ⊆ 𝒞 ∧
      (↑s : Set (Set (EuclideanSpace ℝ (Fin d)))).PairwiseDisjoint id ∧
      volume (⋃₀ (↑𝒞 : Set (Set (EuclideanSpace ℝ (Fin d))))) ≤
        3 ^ d * ∑ B ∈ s, volume B := by sorry

end HardyLittlewoodMaximal
