-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_weighted_high_rank_words
-- name    : OAI.TwoPointCorrelations.eventually_weighted_high_rank_words
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:15:47.229189+00:00
-- url     : https://prove2.me/theorems/bd526a64-f789-4f31-a67e-6c975d956b51
-- title:
--   Weighted column words of high rank contribute at most exp(−L^{203/200}/8)
-- statement:
--   Let $h$ be natural and $C_j,C_m,C_w\ge0$. For all sufficiently large $L$: let $\iota$ be a finite type of labels with injective positive moduli $p:\iota\to\mathbb N$, $p\le Z$; $P_1,\dots,P_J$ pairwise disjoint sets of primes, $Q_p$ a set; $F$ a finite set of column words (column prime assignment, paddings), directions, a column index $j$, a set of perfect rows, a cut, origins, labels, targets, a base, a set $U$ of slots, weights, functions $G$ with $|G|\le1$, caps and $W\in[0,\exp(C_wL\log^2L)]$. Suppose $1\le R\le2L$, $J\le C_j\log L$, $M\le C_m\log L$, $RM+1\le L^2$, $R+1\le L^2$, the harmonic masses are at most $L^2$ and $\sum_{p\in P_j}1/p\ge1$, the primes of $P_j$ lie in $[H,B]$ with $B\le e^L$, $H\ge\exp(L^{199/200})$, paddings are squarefree, at most $Q\le e^{100L+1}$, with at most $M$ prime factors, all in $Q_p$; products of the other columns are at most $D\le e^{2L}$; no column pattern of column $j$ is of low rank (not `ColumnLowRank … perfect cut ⌊L^{1/50}⌋`); the $j$-th column primes divide the displaced origins at the perfect rows; $U$ lies in the non-singleton slots; nonsingleton labels have $p\ge H$; tuple and padding supports are disjoint; the labels' moduli are exactly the word's divisor primes; weights in $[0,\mathrm{cap}]$, nonzero only where `RetainedMainTests` hold; and $\mathrm{cap}\cdot2^{\#\text{singletons}}\le W$. Then
--
--   $$\sum_{a\in F}\texttt{designatedReciprocal}(\dots)\cdot\mathbb E_x\Big[\mathrm{weight}(a,x)\,\big|\texttt{selectedMixedDifference}(\dots)(x)\big|\Big]\le\exp\!\big(-\tfrac18L^{203/200}\big),$$
--
--   the expectation over independent uniform residues modulo the $p(i)$ (`FiniteLaw.independent`, `uniformResidueLaw`), and the mixed difference of $G(a,\cdot)$ with the lit coordinates forced as in the Lean statement.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_weighted_high_rank_words`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_weighted_high_rank_words
    (h : ℕ) (Cj Cm Cw : ℝ) (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (J R M Q D B H Z : ℕ)
      (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (origin : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
      (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpZ : ∀ i, p i ≤ Z)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → ι)
      (target : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → Fin Z)
      (base : ι → Fin Z) (U : Finset (Fin R × Fin J))
      (weight G : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → (ι → Fin Z) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass Qp ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ l, ∀ r ∈ P l, r.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ r ∈ P j, H ≤ r) → (∀ r ∈ P j, r ≤ B) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (B : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i, Squarefree (a.2 i)) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ origin a.1 a.2 +
        wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      Function.Injective p →
      (∀ a ∈ F, U ⊆ nonsingletonSlots (label a)) →
      (∀ a ∈ F, ∀ i ∈ nonsingletonLabels (label a), (H : ℝ) ≤ p i) →
      (∀ a ∈ F, Disjoint (tuplePrimeSupport a.1) (paddingPrimeSupport a.2)) →
      (∀ a ∈ F, ∀ i ∈ univ.image (label a),
        p i ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2)) →
      (∀ a ∈ F, ∀ r ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2), ∃ i, p i = r) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, |G a x| ≤ 1) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        RetainedMainTests p (univ.image (label a)) h Z (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, designatedReciprocal p (singletonLabels (label a))
        (nonsingletonSlots (label a) \ U) U (label a) *
        (FiniteLaw.independent (fun i => uniformResidueLaw Z (p i) (hp i) (hpZ i))).average
          (fun x => weight a x * |selectedMixedDifference (singletonLabels (label a))
            (singletonTarget (label a) (target a) base)
            (fun y => G a (forceCoordinates ((nonsingletonSlots (label a) \ U).image (label a))
              (litForcedTarget (nonsingletonSlots (label a) \ U) (label a) (target a) base) y)) x|)) ≤
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
