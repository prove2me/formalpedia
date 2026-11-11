-- Prove2me | Theorems.Thm_NCQuadLB_sum_choose_le_case_small
-- name    : NCQuadLB.sum_choose_le_case_small
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:50.294256+00:00
-- url     : https://prove2.me/theorems/ebc9d844-e366-4eeb-b209-ad80ea3b522f
-- title:
--   Proof of Theorem 4.2, case $d\le S/2$ — $n^d\le\sum_{k\le d}\binom Sk\le(d+1)\binom Sd\le(d+1)(eS/d)^d$
-- statement:
--   Let $\mathbb F$ be a field, $n\ge2$, $d\ge1$, and let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit computing $\mathrm{Pal}_{n,d}(X,Y)$, with $S$ product gates. Suppose $d\le S/2$. Then
--
--   $$
--   n^d\le\sum_{k=0}^d\binom Sk\le(d+1)\binom Sd\le(d+1)\Bigl(\frac{eS}{d}\Bigr)^d .
--   $$
--
--   This chain gives $S\ge nd/(e(d+1)^{1/d})$ in the case of many product gates.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included. The inequalities are stated in $\mathbb R$.
--
--   Differences from the source:
--
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - generalization: the root of the circuit → a designated output vertex; further vertices, even ones not below the output, are allowed and counted in the size and in the number of product gates; reason: enlarges the class of circuits; a circuit with a single root is the case where every vertex lies below the output
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $d\le S/2$; $e$ → $2d\le S$; $e=\exp 1$; reason: the same condition and constant
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), proof of Theorem 4.2, case d ≤ S/2, p.8

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_pal

namespace NCQuadLB

/-- **Proof of Theorem 4.2, case `d ≤ S/2`** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.8). Let `n ≥ 2`, `d ≥ 1`, let `Ψ` compute
`Pal_{n,d}(X, Y)` with `S` product gates, and suppose `d ≤ S/2`. Then
`n^d ≤ ∑_{k=0}^d (S choose k) ≤ (d + 1) (S choose d) ≤ (d + 1) (eS/d)^d`.

**Formalization Note** `d ≤ S/2` is written `2d ≤ S`. The three inequalities are stated in `ℝ`;
`e = Real.exp 1`. -/
theorem sum_choose_le_case_small {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d))
    (hcase : 2 * d ≤ C.numMul) :
    (n : ℝ) ^ d ≤ ∑ k ∈ Finset.range (d + 1), (C.numMul.choose k : ℝ) ∧
      ∑ k ∈ Finset.range (d + 1), (C.numMul.choose k : ℝ) ≤
        ((d : ℝ) + 1) * (C.numMul.choose d : ℝ) ∧
      ((d : ℝ) + 1) * (C.numMul.choose d : ℝ) ≤
        ((d : ℝ) + 1) * (Real.exp 1 * (C.numMul : ℝ) / d) ^ d := by sorry

end NCQuadLB
