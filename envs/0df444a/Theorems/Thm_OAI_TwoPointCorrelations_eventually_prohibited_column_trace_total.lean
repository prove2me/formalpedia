-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_column_trace_total
-- name    : OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:20.332462+00:00
-- url     : https://prove2.me/theorems/532ebff6-36b0-4070-add6-a25837c5752f
-- title:
--   The total prohibited column trace is bounded by the moment of the good words plus a negligible error
-- statement:
--   Let $h$ be natural and $C,C_e,C_s,C_w\ge0$, $W\ge1$. For all sufficiently large $L$, for every prohibited prime family `data` (`ProhibitedPrimeFamily h J M`), pairwise disjoint prime sets $P_1..P_J\subseteq$ data.P, a set $Q$, a finite set $F$ of column words of even length $2k$ with labels, weights, caps, a cut point, padding weights $u$, eligibility, $g$, $K$, extra predicates, next-step maps and origins, satisfying the long list of size hypotheses of the Lean statement (among them $J\ge1$, $L/2\le k\le L$, $J+M\le C\log L$, bounds by $L^2$ on the harmonic masses and on $2k(J+M)+1$, $1\le\sum_{p\in P_j}1/p\le 2W$, the prime ranges $[H,Y]$ with $H\ge\exp(L^{199/200})$, $Y\le e^L$, the padding and product bounds $Q_{\max}\le e^{100L+1}$, $D_{\max}\le e^{2L}$, $A\le\exp(C_wL\log^2L)$, $0\le$ external $\le e^{C_eL}$, the cap inequalities including the comparison with `crudeTraceWeight` for words with at most $\lfloor L^{1/4}\rfloor$ singleton labels, the main padding tests, $s\ge L^{1/10}/2$, nonbacktracking of the word before and after the cut, and $\mathrm{weight}\le$ `retainedColumnPaddingWeight …`),
--
--   $$e^{108L}\sum_{a\in F}\big|\texttt{prohibitedCenteredAverage}(\dots)\big|\le e^{108L}\big(e^{-L^{21/20}}+2e^{-L^{101/100}}\big)+\big(K(e^{150}\sqrt W)^J\big)^{2k}.$$
--
--   All named objects are definitions of the bundle; the precise hypotheses are those of the Lean statement.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_prohibited_column_trace_total (h : ℕ) (C Ce Cs Cw W : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B s D k n K₀ H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (_hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → ℝ)
      (A external : ℝ) (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((⌊L ^ (1 / 4 : ℝ)⌋₊ + 2 * k * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((2 * k * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      ((2 * k : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ j, P j ⊆ data.P) →
      (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ j, primeHarmonicMass (P j) ≤ L ^ (2 : ℕ)) →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (Dmax : ℝ) ≤ Real.exp (2 * L) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, (a.2 i).val ≤ Qmax) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ Dmax) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ A → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, cap a * 2 ^ (2 * k * J + (singletonLabels (label a)).card) ≤ A) →
      (∀ a ∈ F, (singletonLabels (label a)).card ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊ →
        cap a * 2 ^ (singletonLabels (label a)).card ≤
        crudeTraceWeight (2 * k) ⌊L ^ (1 / 4 : ℝ)⌋₊ (fun i => (a.2 i).val) L external) →
      (∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) → weight a x = weight a y) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      2 * k + n * s ≤ D →
      (∀ a ∈ F, ⌊L ^ (1 / 4 : ℝ)⌋₊ < (singletonLabels (label a)).card →
        n * (s * J) < (singletonLabels (label a)).card) →
      (D : ℝ) ≤ 4 * L → 0 < n → (n : ℝ) ≤ 4 * L → 8 * K₀ ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K₀ : ℝ) → (K₀ : ℝ) ≤ L →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) * (∑ a ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) (weight a)|) ≤
        Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
          2 * Real.exp (-L ^ (101 / 100 : ℝ))) +
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  sorry

end OAI.TwoPointCorrelations
