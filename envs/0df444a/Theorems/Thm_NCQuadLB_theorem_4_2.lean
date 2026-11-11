-- Prove2me | Theorems.Thm_NCQuadLB_theorem_4_2
-- name    : NCQuadLB.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:54.676918+00:00
-- url     : https://prove2.me/theorems/5391d533-96f2-43cd-9e09-9184bd7b30b6
-- title:
--   Theorem 4.2 (with Theorem 1.2) — circuits for $\mathrm{Pal}_{n,d}$ have at least $nd/6$ product gates, hence size $\Omega(nd)$
-- statement:
--   Let $\mathbb F$ be any field, $n\ge2$ and $d\ge1$, and let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit (with edge scalars) computing the palindrome polynomial $\mathrm{Pal}_{n,d}(X,Y)$. Then $\Psi$ has $S=\Omega(nd)$ product gates, and hence size $\Omega(nd)$; explicitly,
--
--   $$
--   nd\le6\,S\qquad\text{and}\qquad nd\le6\cdot\mathrm{size}(\Psi).
--   $$
--
--   At $d=n$ this is the quadratic lower bound $\Omega(n^2)$ for general noncommutative circuits; since $\mathrm{Pal}_{n,d}$ has circuits of size $O(nd)$, the bound is tight up to the constant.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included. The constant $6$ is absolute: it does not depend on $\mathbb F$, $n$, $d$ or the circuit.
--
--   Differences from the source:
--
--   - generalization: $S=\Omega(nd)$ product gates (Theorem 4.2) and size $\Omega(nd)$ (Theorem 1.2) → $nd\le6S$ and $nd\le6\cdot\mathrm{size}$ for every field, every $n\ge2$, $d\ge1$ and every circuit; reason: the source's proof ends with "$S\ge(nd)/6$"; an explicit absolute constant implies $\Omega(nd)$
--   - reading: Theorem 1.2 states size $\Omega(nd)$ with no range of $n,d$ → the size bound under Theorem 4.2's $n\ge2$, $d\ge1$; reason: at $n=1$, $\mathrm{Pal}_{1,d}=x^dy^d$ has circuits of size $O(\log d)$ by repeated squaring, so $\Omega(nd)$ needs $n\ge2$; at $d=0$ the bound is empty
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - generalization: the root of the circuit → a designated output vertex; further vertices, even ones not below the output, are allowed and counted in the size and in the number of product gates; reason: enlarges the class of circuits; a circuit with a single root is the case where every vertex lies below the output
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Theorem 4.2, p.8; Theorem 1.2, p.3

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_pal

namespace NCQuadLB

/-- **Theorem 4.2**, with **Theorem 1.2** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, Theorem 4.2, p.8; Theorem 1.2, p.3). Let `n ≥ 2`
and `d ≥ 1`, and let `Ψ` be a fan-in 2 noncommutative arithmetic circuit computing `Pal_{n,d}(X, Y)`.
Then `Ψ` has `S = Ω(nd)` many product gates; hence `Ψ` has size `Ω(nd)`.

**Formalization Note** `Ω(nd)` is stated with the explicit absolute constant of the source's proof
("`S ≥ … ≥ (nd)/6`"): `n·d ≤ 6·S` and `n·d ≤ 6·size`, for every field `F`, every `n ≥ 2`, `d ≥ 1` and
every circuit; the constant depends on nothing. Circuits are `Circuit F (Fin n ⊕ Fin n)`
(Definition 2.2: vertices in topological order, a scalar on every in-edge, both in-edges of a gate may
come from one vertex, a designated output vertex); `S` is `numMul`, the number of `×` gates, and the
size is the number of vertices, leaves included. `Pal_{n,d}` is `pal F n d` (`x_j = ι (Sum.inl j)`,
`y_j = ι (Sum.inr j)`). -/
theorem theorem_4_2 {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (C : Circuit F (Fin n ⊕ Fin n)) (hC : C.Computes (pal F n d)) :
    n * d ≤ 6 * C.numMul ∧ n * d ≤ 6 * C.size := by sorry

end NCQuadLB
