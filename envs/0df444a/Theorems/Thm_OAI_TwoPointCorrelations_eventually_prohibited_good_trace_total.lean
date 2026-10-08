-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_good_trace_total
-- name    : OAI.TwoPointCorrelations.eventually_prohibited_good_trace_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:58.41259+00:00
-- url     : https://prove2.me/theorems/3ee5cb4b-b92a-472f-b4cb-bb5eca98ee77
-- title:
--   The designated terms of the low-rank column words are bounded by the good-word moment
-- statement:
--   Let $W\ge1$. For all sufficiently large $L$: let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with primes at most $B$, $P_1,\dots,P_J$ pairwise disjoint sets of primes with $\sum_{p\in P_j}1/p\le2W$, $Q$ a set, $F$ a finite set of column words $a$ of even length $2k$ (a column prime assignment and paddings in $Q$) whose columns are pairs of the family, with labels agreeing with the assignment, a base, weights $\ge0$ depending only on the labelled primes, nonzero only where `MainPaddingTests` hold, bounded by `retainedColumnPaddingWeight Q u eligible g L K extra next (origin x)`, a cut point, $u\ge0$, $K\ge0$, and suppose $J\ge1$, $L/2\le k\le L$, $S\le L^{1/4}$, $2k\le D$, $h,s>0$, $s\ge L^{1/10}/2$, the word is nonbacktracking (consecutive tuples differ) before and after the cut, and every word has at most $S$ column singletons (`columnSingletonCount`). Then
--
--   $$e^{108L}\sum_{a\in F}\ \sum_{U}\texttt{prohibitedDesignatedTerm}(\mathrm{data},s,D,\texttt{columnTupleWord}(a),\mathrm{label}(a),\mathrm{base},\mathrm{weight}(a),U)\le\big(K(e^{150}\sqrt W)^J\big)^{2k},$$
--
--   where $U$ runs over the sets of non-singleton slots of $a$ with at most $\lfloor L^{1/50}\rfloor$ elements for which every column pattern is of low rank (`ColumnLowRank … (perfectRows (label a) U) cut ⌊L^{1/50}⌋`). All named objects are bundle definitions.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_prohibited_good_trace_total`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_prohibited_good_trace_total (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B s D k S : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      2 * k ≤ D → (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      (∀ a ∈ F, ∀ y z, (∀ i, i ∉ univ.image (label a) → y i = z i) → weight a y = weight a z) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ a ∈ F, columnSingletonCount a.1 ≤ S) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) *
        (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ∀ j, ColumnLowRank
            (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
            hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
          prohibitedDesignatedTerm data hB s D
            (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base (weight a) U) ≤
      (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  sorry

end OAI.TwoPointCorrelations
