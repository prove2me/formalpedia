-- Prove2me | Theorems.Thm_NearLinIsing_lemma_3_8
-- name    : NearLinIsing.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:06.724503+00:00
-- url     : https://prove2.me/theorems/c310148b-cc42-491e-a1ea-26c1680eb712
-- title:
--   Lemma 3.8 — event bounds
-- statement:
--   Let $(E_i)$ be measurable events on a probability space with probabilities $p_i>0$, and let a conflict graph be such that, for every finite index set $T$,
--
--   $$\mathbb P\Big(\bigcap_{i\in T}E_i\Big)=\prod_{i\in T}p_i\ \text{ if $T$ is independent},\qquad\text{and } 0\text{ otherwise}.$$
--
--   Suppose at most $K$ events occur simultaneously. Then for every partition $L\cup R$ of the indices,
--
--   $$\Big\|\big(\sqrt{p_ip_j}\,\mathbf 1\{i\in N(j)\}\big)_{i\in L,\,j\in R}\Big\|\le\frac56,\qquad \sum_ip_i\exp\Big(\frac12\sum_{j\in N[i]}p_j\Big)\le2\sqrt e\,K,$$
--
--   where $N(i)$ and $N[i]$ are the open and closed conflict neighbourhoods. The lemma gives a lower spectral bound and an exponential activity estimate whenever conflicts are encoded by mutually exclusive events.
--
--   Differences from the source:
--   - generalization: events E_i (the uses are finite families) → any countable index type; reason: the finite case is an instance
--   - generalization: at most K events occur simultaneously → at most K events occur, almost surely; reason: the pointwise reading implies the almost-sure one
--   - encoding: operator norm at most 5/6 → the bilinear bound |xᵀMy| ≤ (5/6)‖x‖‖y‖ over finitely supported x on L and y off L; reason: this is the operator norm, and it also covers infinite index sets
--   - encoding: the activity sum → the sum is asserted summable and then bounded; reason: a divergent `tsum` would otherwise read 0
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 3.8, p. 17

import Mathlib

open MeasureTheory

namespace NearLinIsing

open Classical in
/-- **Lemma 3.8** (Event bounds), p. 17.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 3.8, p. 17.

Let `(E_i)` be measurable events on a probability space with probabilities `p_i > 0` and a
conflict graph such that for every finite set `T` of indices `P(⋂_{i∈T} E_i) = ∏_{i∈T} p_i` when `T`
is independent and `0` otherwise. Suppose at most `K` events occur simultaneously. Then for every
partition `L ∪ R` of the indices the matrix `(√(p_i p_j) 1{i ∈ N(j)})_{i ∈ L, j ∈ R}` has operator
norm at most `5/6`, and `∑_i p_i exp(½ ∑_{j ∈ N[i]} p_j) ≤ 2√e K`, with `N(i)`, `N[i]` the open
and closed conflict neighbourhoods.

**Formalization Note.** Reading R10: the index set is any countable type (the paper's uses are
finite; the finite case is a special case, and the countable one follows from it by restriction).
The operator-norm bound is stated as the bilinear bound `|xᵀ M y| ≤ (5/6) ‖x‖ ‖y‖` over finitely
supported `x` on `L` and `y` on `R`. The activity sum is stated with its summability, so a
divergent sum cannot satisfy it by the `tsum` default. "At most `K` events occur simultaneously" is
assumed almost surely, which the pointwise reading implies. -/
theorem lemma_3_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (Gc : SimpleGraph ι) (hpos : ∀ i, 0 < μ.real (E i))
    (hjoint : ∀ T : Finset ι, μ.real (⋂ i ∈ T, E i) =
      if (∀ i ∈ T, ∀ j ∈ T, ¬ Gc.Adj i j) then ∏ i ∈ T, μ.real (E i) else 0)
    (K : ℕ) (hK : ∀ᵐ ω ∂μ, ∀ T : Finset ι, (∀ i ∈ T, ω ∈ E i) → T.card ≤ K) :
    (∀ L : Set ι, ∀ x y : ι →₀ ℝ, (∀ i ∈ x.support, i ∈ L) → (∀ j ∈ y.support, j ∉ L) →
      |∑ i ∈ x.support, ∑ j ∈ y.support,
          x i * (Real.sqrt (μ.real (E i) * μ.real (E j)) * (if Gc.Adj i j then 1 else 0)) * y j| ≤
        5 / 6 * Real.sqrt (∑ i ∈ x.support, x i ^ 2) * Real.sqrt (∑ j ∈ y.support, y j ^ 2)) ∧
    Summable (fun i => μ.real (E i) *
      Real.exp (1 / 2 * ∑' j : {j : ι // j = i ∨ Gc.Adj i j}, μ.real (E j))) ∧
    ∑' i, μ.real (E i) * Real.exp (1 / 2 * ∑' j : {j : ι // j = i ∨ Gc.Adj i j}, μ.real (E j)) ≤
      2 * Real.sqrt (Real.exp 1) * K := by sorry

end NearLinIsing
