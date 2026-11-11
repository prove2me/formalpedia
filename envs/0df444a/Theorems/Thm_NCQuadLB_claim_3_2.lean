-- Prove2me | Theorems.Thm_NCQuadLB_claim_3_2
-- name    : NCQuadLB.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:14.103359+00:00
-- url     : https://prove2.me/theorems/8ee07ff5-c6e4-48de-97a2-49c7b6166305
-- title:
--   Claim 3.2 — $\mathrm{Coeff}_X(\hat g_{XY})\subseteq\mathrm{span}(\mathcal B_g)$
-- statement:
--   Let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit over $\mathbb F\langle X,Y\rangle$, with edge scalars. For every vertex $g$ of $\Psi$,
--
--   $$
--   \mathrm{Coeff}_X(\hat g_{XY})\subseteq\mathrm{span}_{\mathbb F}(\mathcal B_g),
--   $$
--
--   where $\hat g$ is the polynomial computed at $g$, $\hat g_{XY}$ its $X,Y$-separated part and $\mathcal B_g$ the set of Definition 3.1. No assumption is made on what the circuit computes.
--
--   At the output of a circuit computing $\mathrm{Pal}_{n,d}$ this puts the whole coefficient space of $\mathrm{Pal}_{n,d}$ inside $\mathrm{span}(\mathcal B_r)$.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included.
--
--   Differences from the source:
--
--   - generalization: for every gate $g$ → for every vertex $g$, leaves included; reason: the leaves are the base case of the source's proof; the gates are the source's statement
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $\mathbb F\langle X\rangle$ → the polynomials of $\mathbb F\langle X,Y\rangle$ in the $X$-variables only; spans are taken inside $\mathbb F\langle X,Y\rangle$; reason: $\mathbb F\langle X\rangle\to\mathbb F\langle X,Y\rangle$ is an injective algebra map, so spans and dimensions agree
--   - encoding: $\mathrm{coeff}_m(f)$ defined for $X,Y$-separated $f$ → $\mathrm{coeff}_m(f)=\sum_{u\in X\text{-words}}[u\,m]f\cdot u$ for every $f$; reason: on separated $f$ this is the source's $c_m$; it is applied only to separated polynomials here
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Claim 3.2, p.6

import Mathlib
import Definitions.Def_NCQuadLB_Circuit_B

namespace NCQuadLB

/-- **Claim 3.2** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.6). For every gate `g`, `Coeff_X(ĝ_{XY}) ⊆ span(ℬ_g)`.

**Formalization Note** Stated for every fan-in 2 circuit with edge scalars over
`F⟨X, Y⟩ = FreeAlgebra F (Fin n ⊕ Fin n)` (`X = Sum.inl`, `Y = Sum.inr`) and every vertex `g`,
leaves included (the source's proof treats leaves as its base case). No hypothesis on what the circuit
computes. `ĝ` is `value g`, `ĝ_{XY}` is `xyPart`, `ℬ_g` is `B g` (Definition 3.1) and the span is
the `F`-linear span inside `F⟨X, Y⟩`. -/
theorem claim_3_2 {F : Type*} [Field F] {n : ℕ} (C : Circuit F (Fin n ⊕ Fin n))
    (g : Fin C.size) :
    CoeffX (xyPart (C.value g)) ⊆ Submodule.span F (C.B g) := by sorry

end NCQuadLB
