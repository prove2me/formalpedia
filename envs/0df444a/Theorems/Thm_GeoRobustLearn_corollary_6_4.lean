-- Prove2me | Theorems.Thm_GeoRobustLearn_corollary_6_4
-- name    : GeoRobustLearn.corollary_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:02.758303+00:00
-- url     : https://prove2.me/theorems/81afbf93-8b21-4b38-a270-95fe935138f4
-- title:
--   Corollary 6.4 — $k$-way consensus splitting of $q$ nonatomic measures on $\mathbb R$ with $\le2q(k-1)$ cuts
-- statement:
--   Let $q,k\ge1$, let $\nu_1,\dots,\nu_q$ be nonatomic finite measures on $\mathbb R$, and let $\vec w\in\Delta_k$ (that is, $w_i\ge0$ and $\sum_iw_i=1$). Then there are a finite set $T\subset\mathbb R$ of at most $2q(k-1)$ cutpoints and a partition $B_1,\dots,B_k$ of $\mathbb R$ such that
--
--   $$\nu_j(B_i)=w_i\,\nu_j(\mathbb R)\qquad(j\in[q],\ i\in[k]),$$
--
--   and membership in each $B_i$ is constant between consecutive cutpoints. In particular every part is a finite union of intervals.
--
--   This necklace-splitting statement, a corollary of [SW85], is what guarantees that a strip partition with a bounded number of seams can reproduce the threshold mixture.
--
--   Differences from the source:
--   - encoding: "determined by at most 2q(k − 1) cutpoints" → a finite T with |T| ≤ 2q(k − 1) such that for x, y ∉ T with no point of T in [x, y], x ∈ B_i ↔ y ∈ B_i; reason: each cutpoint may belong to either neighbouring part, as the proof says (p.35); the finite-union-of-intervals clause follows
--   - encoding: partition B_1, …, B_k of ℝ → pairwise disjoint sets with union ℝ (empty parts allowed); reason: the proof sets B_i = ∅ when w_i = 0
--   - reading: q measures, w⃗ ∈ Δ_k → q, k ≥ 1; reason: Δ_k is empty at k = 0; q counts measures
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Corollary 6.4, p.34 (PDF p.34)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace GeoRobustLearn

/-- **Corollary 6.4**, p.34.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

For `q` nonatomic finite measures `ν_1, …, ν_q` on `ℝ` and any `w⃗ ∈ Δ_k`, there is a partition
`B_1, …, B_k` of `ℝ`, determined by at most `2q(k − 1)` cutpoints, such that
`ν_j(B_i) = w_i ν_j(ℝ)` for all `j ∈ [q]`, `i ∈ [k]`.

**Formalization Note.** "Determined by the cutpoints `T`" means: membership in each `B_i` is
constant between consecutive cutpoints, i.e. for `x, y ∉ T` with no point of `T` in `[x, y]`,
`x ∈ B_i ↔ y ∈ B_i` (each cutpoint itself may go to either part). Then every part is a finite union
of intervals and points. The parts are pairwise disjoint and cover `ℝ`; `Δ_k` is the standard
simplex. `q, k ≥ 1`. -/
theorem corollary_6_4 (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) (ν : Fin q → Measure ℝ)
    (hfin : ∀ j, IsFiniteMeasure (ν j)) (hna : ∀ j, NullSingletonClass (ν j))
    (w : Fin k → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∃ (T : Finset ℝ) (B : Fin k → Set ℝ),
      T.card ≤ 2 * q * (k - 1) ∧
      Pairwise (fun i i' => Disjoint (B i) (B i')) ∧
      (⋃ i, B i) = Set.univ ∧
      (∀ i, ∀ x y : ℝ, x ∉ T → y ∉ T → (∀ t ∈ T, t ∉ Set.uIcc x y) → (x ∈ B i ↔ y ∈ B i)) ∧
      ∀ j i, ν j (B i) = ENNReal.ofReal (w i) * ν j Set.univ := by sorry

end GeoRobustLearn
