-- Prove2me | Theorems.Thm_NCQuadLB_pal_dim_le_sum_choose
-- name    : NCQuadLB.pal_dim_le_sum_choose
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:47.223192+00:00
-- url     : https://prove2.me/theorems/d0cd3899-8dd6-4e2e-b8ba-0716319b3c4a
-- title:
--   Proof of Theorem 4.2 — $n^d\le\sum_{k=0}^d\binom Sk$
-- statement:
--   Let $\mathbb F$ be a field, $n\ge2$, $d\ge1$, and let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit computing $\mathrm{Pal}_{n,d}(X,Y)$, with $S$ product gates. Comparing Lemma 4.1 with $\dim_{\mathbb F}\mathrm{span}\{\mathrm{Coeff}_X(\mathrm{Pal}_{n,d})\}=n^d$ gives
--
--   $$
--   n^d\le\sum_{k=0}^d\binom Sk.
--   $$
--
--   It is the inequality from which the numerical lower bound on $S$ is derived; the source writes it in each of its two cases, and it is stated here with no case hypothesis.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included.
--
--   Differences from the source:
--
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - generalization: the root of the circuit → a designated output vertex; further vertices, even ones not below the output, are allowed and counted in the size and in the number of product gates; reason: enlarges the class of circuits; a circuit with a single root is the case where every vertex lies below the output
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), proof of Theorem 4.2, p.8

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_pal

namespace NCQuadLB

/-- **Proof of Theorem 4.2, the counting inequality** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.8). Let `n ≥ 2`, `d ≥ 1`, and let `Ψ`
be a fan-in 2 noncommutative arithmetic circuit computing `Pal_{n,d}(X, Y)` with `S` product gates.
Comparing the bound of Lemma 4.1 with `dim_F span{Coeff_X(Pal_{n,d})} = n^d` gives
`n^d ≤ ∑_{k=0}^d (S choose k)`.

**Formalization Note** Stated with no case hypothesis (the source prints it in both cases `d ≤ S/2`
and `S/2 < d`). `S` is `numMul`, the number of `×` gates. -/
theorem pal_dim_le_sum_choose {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d)) :
    n ^ d ≤ ∑ k ∈ Finset.range (d + 1), C.numMul.choose k := by sorry

end NCQuadLB
