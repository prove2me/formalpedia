-- Prove2me | Theorems.Thm_NCQuadLB_lemma_4_1
-- name    : NCQuadLB.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:34.264467+00:00
-- url     : https://prove2.me/theorems/27a7835f-2a99-4600-8a24-75364643fc23
-- title:
--   Lemma 4.1 — $\pi_d(\mathcal B_r)$ is spanned by at most $\sum_{k=0}^d\binom Sk$ elements
-- statement:
--   Let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit over $\mathbb F\langle X,Y\rangle$ with root $r$ and at most $S$ product gates, and let $d\ge0$. Then $\pi_d(\mathcal B_r)$ is spanned by a set of size at most
--
--   $$
--   \sum_{k=0}^d\binom Sk:
--   $$
--
--   there is a finite set $T$ with $|T|\le\sum_{k=0}^d\binom Sk$ and $\mathrm{span}\,T=\mathrm{span}\,\pi_d(\mathcal B_r)$.
--
--   This is the upper bound on the dimension that the lower bound compares with $n^d$.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included. The root $r$ is the output vertex.
--
--   Differences from the source:
--
--   - reading: "$\pi_d(\mathcal B_r)$ is spanned by a set of size at most $\sum_{k=0}^d\binom Sk$" → a finite $T$ with $|T|\le\sum_{k=0}^d\binom Sk$ and $\mathrm{span}\,T=\mathrm{span}\,\pi_d(\mathcal B_r)$; reason: equivalent to $\pi_d(\mathcal B_r)\subseteq\mathrm{span}\,T$ (pick a basis of $\mathrm{span}\,\pi_d(\mathcal B_r)$ inside $\pi_d(\mathcal B_r)$); the equality form is not weaker
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - generalization: the root of the circuit → a designated output vertex; further vertices, even ones not below the output, are allowed and counted in the size and in the number of product gates; reason: enlarges the class of circuits; a circuit with a single root is the case where every vertex lies below the output
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $\mathbb F\langle X\rangle$ → the polynomials of $\mathbb F\langle X,Y\rangle$ in the $X$-variables only; spans are taken inside $\mathbb F\langle X,Y\rangle$; reason: $\mathbb F\langle X\rangle\to\mathbb F\langle X,Y\rangle$ is an injective algebra map, so spans and dimensions agree
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Lemma 4.1, p.7

import Mathlib
import Definitions.Def_NCQuadLB_Circuit_B

namespace NCQuadLB

/-- **Lemma 4.1** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.7). Let `Ψ` be a circuit with root `r` and at most `S` product gates.
Then `π_d(ℬ_r)` is spanned by a set of size at most `∑_{k=0}^d (S choose k)`.

**Formalization Note** The root `r` is the output vertex. "`π_d(ℬ_r)` is spanned by a set `T`" is
read as `span T = span π_d(ℬ_r)`, with `T` a finite set of polynomials. Every `d ∈ ℕ` and every circuit
over `F⟨X, Y⟩ = FreeAlgebra F (Fin n ⊕ Fin n)` are allowed. -/
theorem lemma_4_1 {F : Type*} [Field F] {n : ℕ} (C : Circuit F (Fin n ⊕ Fin n)) (S : ℕ)
    (hS : C.numMul ≤ S) (d : ℕ) :
    ∃ T : Finset (FreeAlgebra F (Fin n ⊕ Fin n)),
      T.card ≤ ∑ k ∈ Finset.range (d + 1), S.choose k ∧
      Submodule.span F (T : Set (FreeAlgebra F (Fin n ⊕ Fin n))) =
        Submodule.span F (proj d '' C.B C.output) := by sorry

end NCQuadLB
