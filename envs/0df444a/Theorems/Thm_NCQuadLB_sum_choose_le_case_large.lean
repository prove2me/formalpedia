-- Prove2me | Theorems.Thm_NCQuadLB_sum_choose_le_case_large
-- name    : NCQuadLB.sum_choose_le_case_large
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:49.647098+00:00
-- url     : https://prove2.me/theorems/f3418c0a-57c7-49ce-8dce-704afdd7f300
-- title:
--   Proof of Theorem 4.2, case $S/2<d$ — $n^d\le\sum_{k\le d}\binom Sk\le(d+1)\binom S{\lfloor S/2\rfloor}\le(d+1)2^S$
-- statement:
--   Let $\mathbb F$ be a field, $n\ge2$, $d\ge1$, and let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit computing $\mathrm{Pal}_{n,d}(X,Y)$, with $S$ product gates. Suppose $S/2<d$. Then
--
--   $$
--   n^d\le\sum_{k=0}^d\binom Sk\le(d+1)\binom S{\lfloor S/2\rfloor}\le(d+1)2^S .
--   $$
--
--   This chain bounds $S$ from below in the case of few product gates.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included. The inequalities are stated in $\mathbb N$.
--
--   Differences from the source:
--
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - generalization: the root of the circuit → a designated output vertex; further vertices, even ones not below the output, are allowed and counted in the size and in the number of product gates; reason: enlarges the class of circuits; a circuit with a single root is the case where every vertex lies below the output
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $S/2<d$; $\lfloor S/2\rfloor$ → $S<2d$; the natural-number quotient $S/2$; reason: the same condition and the same integer
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), proof of Theorem 4.2, case S/2 < d, p.8

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_pal

namespace NCQuadLB

/-- **Proof of Theorem 4.2, case `S/2 < d`** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.8). Let `n ≥ 2`, `d ≥ 1`, let `Ψ` compute
`Pal_{n,d}(X, Y)` with `S` product gates, and suppose `S/2 < d`. Then
`n^d ≤ ∑_{k=0}^d (S choose k) ≤ (d + 1) (S choose ⌊S/2⌋) ≤ (d + 1) 2^S`.

**Formalization Note** `S/2 < d` is written `S < 2d`; `⌊S/2⌋` is the natural-number quotient `S / 2`.
The inequalities are in `ℕ`. -/
theorem sum_choose_le_case_large {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d))
    (hcase : C.numMul < 2 * d) :
    n ^ d ≤ ∑ k ∈ Finset.range (d + 1), C.numMul.choose k ∧
      ∑ k ∈ Finset.range (d + 1), C.numMul.choose k ≤ (d + 1) * C.numMul.choose (C.numMul / 2) ∧
      (d + 1) * C.numMul.choose (C.numMul / 2) ≤ (d + 1) * 2 ^ C.numMul := by sorry

end NCQuadLB
