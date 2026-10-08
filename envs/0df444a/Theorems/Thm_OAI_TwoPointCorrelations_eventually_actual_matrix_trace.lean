-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_actual_matrix_trace
-- name    : OAI.TwoPointCorrelations.eventually_actual_matrix_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:13.497228+00:00
-- url     : https://prove2.me/theorems/59fe41da-729e-40a2-b8b8-94bd1aaf4681
-- title:
--   The Frobenius moment of the shifted walk matrix of the actual prohibited-prime model
-- statement:
--   Let $h\ge1$, $C\ge0$, $W\ge1$. For all sufficiently large $L$ the following holds. Let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with all primes at most $B$, $P_1,\dots,P_J\subseteq$ data.P pairwise disjoint sets of primes and $Q$ a set of squarefree numbers with prime factors in data.Q, and suppose: $J\ge1$, $J+M\le C\log L$, $1\le\sum_{p\in P_j}1/p\le\min(2W,L^2)$ for all $j$, $1\le\sum_{p\in\mathrm{data}.P}1/p\le L^2$, $\sum_{p\in\mathrm{data}.Q}1/p\le L^2$, $M\le100\log L$, all primes of data.P lie in $[H,Y]$ with $1\le Y\le e^L$ and $H\ge\exp(L^{199/200})$, every padding $q$ of a pair is at most $Q_{\max}\le e^{100L+1}$, every product of $J-1$ chosen primes is at most $D_{\max}\le e^{2L}$. Let $u:\mathbb N\to\mathbb R$ with $0\le u\le$ `crudePaddingWeight`, $g:\mathbb Z\to\mathbb R$ with $g^2\ge1$ and depending only on residues modulo the primes of data.Q, $K\ge1$, `extra` a predicate also depending only on those residues, `eligible` pairs belonging to data.pairs, $V$ a finite type injecting into (tuples)$\times\mathbb Z$ with $|V|\le e^{106L}$, and `gate` any relation. With $s=\lfloor L^{1/10}\rfloor$ and the weight `maskedSignedIntegerWeight …` as written in the statement,
--
--   $$\mathbb E_{r}\Big\|\,\texttt{shiftMatrix}(\dots)(\dots+\mathrm{origin}(r))^{\lfloor L\rfloor}\Big\|_F^2\le\Big(K\,(2e^{150}\sqrt W)^J\Big)^{2\lfloor L\rfloor},$$
--
--   the expectation over the family's residue law `data.residueLaw B hB` and $\|\cdot\|_F^2$ the squared Frobenius norm (`matrixFrobeniusSq`) of the $\lfloor L\rfloor$-th power of the shift matrix built from `integerShiftNext` and `physicalShiftWeight`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_actual_matrix_trace`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_actual_matrix_trace (h : ℕ) (C W : ℝ)
    (hh : 0 < h) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (_hP : ∀ j, P j ⊆ data.P),
      1 ≤ J → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
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
      (∀ dq ∈ data.pairs, dq.2 ≤ Qmax) →
      (∀ w : (j : Fin J) → P j, ∀ j, (∏ l ∈ univ.erase j, (w l).val) ≤ Dmax) →
      (∀ q ∈ Q, Squarefree q) → (∀ q ∈ Q, q.primeFactors ⊆ data.Q) →
      ∀ (u : ℕ → ℝ) (g : ℤ → ℝ) (K : ℝ)
        (eligible : ℕ → ℕ → Prop) (extra : ℕ → ℤ → Prop),
      (∀ q, 0 ≤ u q) → (∀ q, u q ≤ crudePaddingWeight q) →
      (∀ n, 1 ≤ (g n) ^ 2) → 1 ≤ K →
      (∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m) →
      (∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
        (extra d n ↔ extra d m)) →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
      (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
      ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop),
      (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
      let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
      let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
      let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
        L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  sorry

end OAI.TwoPointCorrelations
