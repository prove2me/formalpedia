-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_matrix_residue_trace_of_column_bounds
-- name    : OAI.TwoPointCorrelations.matrix_residue_trace_of_column_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:50.331895+00:00
-- url     : https://prove2.me/theorems/52e6432d-2660-411a-8223-fba88df186ed
-- title:
--   Column trace bounds imply the Frobenius moment bound for the shifted walk matrix
-- statement:
--   Let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) whose primes are at most $B$; let $P_1,\dots,P_J\subseteq$ data.P be pairwise disjoint sets of primes; let $s$, budget, $k$ be naturals with $0<2k\le$ budget; let $V$ be a finite type with an injection `embed` into (tuples)$\times\mathbb Z$; let $Q$ be a set of squarefree numbers with prime factors in data.Q, $u:\mathbb N\to\mathbb R$, an eligibility relation contained in data.pairs, $g:\mathbb Z\to\mathbb R$ nowhere zero and depending only on residues modulo the primes of data.Q, reals $L,K,T$ with $T\ge0$, a predicate `extra` depending only on those residues, and a gate relation. Suppose $|V|\,2^{2k}\le e^{108L}$ and, for every start $x$ and every direction choice `forward` of length $2k$,
--
--   $$e^{108L}\sum_{a}\big|\texttt{prohibitedCenteredAverage}(\mathrm{data},s,\mathrm{budget},\texttt{columnTupleWord}(a),\texttt{actualColumnLabel},\texttt{actualColumnWeight})\big|\le T,$$
--
--   the sum over the closed trace fibre `closedTraceFiber Q (actualClosedPairCatalog …) forward`. Then, with the weight `maskedSignedIntegerWeight Q u eligible g (centeredTuple ∘ primeFactors) L K extra h (non-prohibited sites)`,
--
--   $$\mathbb E_r\Big\|\texttt{shiftMatrix}\big(\mathrm{embed},\texttt{integerShiftNext},\texttt{physicalShiftWeight}(\dots,\mathrm{weight}(\cdot+\mathrm{origin}(r)))\big)^k\Big\|_F^2\le T,$$
--
--   the expectation over `data.residueLaw B hB` and $\|\cdot\|_F^2$ the squared Frobenius norm.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.matrix_residue_trace_of_column_bounds`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem matrix_residue_trace_of_column_bounds {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s budget : ℕ) (hk : 0 < 2 * k) (hbudget : 2 * k ≤ budget)
    (embed : V → ((j : Fin J) → P j) × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K T : ℝ) (extra : ℕ → ℤ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n, g n ≠ 0)
    (hgdep : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (hallowed : ∀ d q, eligible d q → (d, q) ∈ data.pairs)
    (hT : 0 ≤ T)
    (hdim : (Fintype.card V : ℝ) * (2 : ℝ) ^ (2 * k) ≤ Real.exp (108 * L))
    (hcolumn : ∀ (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool),
      Real.exp (108 * L) * (∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) ≤ T) :
    let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
    let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
    (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
      (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
        (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤ T := by
  sorry

end OAI.TwoPointCorrelations
