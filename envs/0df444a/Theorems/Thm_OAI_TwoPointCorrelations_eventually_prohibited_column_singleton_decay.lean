-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_column_singleton_decay
-- name    : OAI.TwoPointCorrelations.eventually_prohibited_column_singleton_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:32.405774+00:00
-- url     : https://prove2.me/theorems/56146a04-e699-4ea6-a1c7-d238beb321c4
-- title:
--   Column words with many singleton labels contribute negligibly to the prohibited centered averages
-- statement:
--   Let $C_s,C_w\ge0$. For all sufficiently large $L$: let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with primes at most $B$; $P_1,\dots,P_J$ pairwise disjoint sets of primes; $F$ a finite set of pairs $w$ = (column prime assignment, padding choice in $Q$) of length $R$; for each $w$ a labelling of $\{1..R\}\times\{1..J\}$ by $P\cup Q$ agreeing with the column assignment, a weight function of the residue data and a cap. Suppose $A\ge0$; the weights are nonnegative, at most the cap, depend only on the labelled primes and are nonzero only where the main padding tests `MainPaddingTests` hold; $\mathrm{cap}(w)\,2^{RJ+\#\text{singleton labels}(w)}\le A\le\exp(C_wL\log^2L)$; each column pair is a pair of the family; $R+ns\le D\le4L$; $ns J<\#$singleton labels of every $w$; $J+M\le C_s\log L$; $0<n\le4L$, $8K\le n$, $L^{1/12}/32\le K\le L$; $1\le\sum_{p\in\mathrm{data}.P}1/p\le L^2$, $\sum_{p\in\mathrm{data}.Q}1/p\le L^2$; and all primes of data.P lie in $[H,Y]$ with $1\le Y\le e^L$, $H\ge\exp(L^{199/200})$. Then
--
--   $$\sum_{w\in F}\Big|\texttt{prohibitedCenteredAverage}(\mathrm{data},s,D,\texttt{columnTupleWord}(w),\mathrm{label}(w),\mathrm{weight}(w))\Big|\le\exp(-L^{21/20}).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_prohibited_column_singleton_decay`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_prohibited_column_singleton_decay (Cs Cw : ℝ)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (forward : Fin R → Bool)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (A : ℝ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      0 ≤ A → (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) → (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, cap w * 2 ^ (R * J + (singletonLabels (label w)).card) ≤ A) →
      (∀ w ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label w) → x i = y i) → weight w x = weight w y) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) x) →
      (∀ w ∈ F, ∀ i, (columnTuple w.1 i, (w.2 i).val) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i j, (label w (i, j)).val = (w.1 j i).val) →
      R + n * s ≤ D → (∀ w ∈ F, n * (s * J) < (singletonLabels (label w)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ w ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) (label w) (weight w)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
