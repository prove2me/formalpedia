-- Prove2me | Theorems.Thm_NCQuadLB_lemma_3_3
-- name    : NCQuadLB.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:13.391708+00:00
-- url     : https://prove2.me/theorems/96c1ac61-b72e-42d1-ad71-de332e9ac3ff
-- title:
--   Lemma 3.3 — $\mathcal B_v=\{w_\pi\mid\pi$ a path from $v$ to a leaf$\}$
-- statement:
--   Let $\Psi$ be a fan-in 2 noncommutative arithmetic circuit over $\mathbb F\langle X,Y\rangle$. For every vertex $v$,
--
--   $$
--   \mathcal B_v=\{w_\pi\mid\pi\text{ is a path from }v\text{ to a leaf}\},
--   $$
--
--   where for a path $\pi=(v_0,\dots,v_m)$ with $v_0=v$ and $v_m$ a leaf, $w_\pi=\prod_{i=0}^m c_{v_i}$ with $c_{v_i}=(\hat a_i)_X$ if $v_i=a_i\times b_i$ is a product gate and $v_{i+1}=b_i$, and $c_{v_i}=1$ otherwise.
--
--   Every element of $\mathcal B_v$ is thus a product of $X$-parts of left children of the product gates at which a path turns right, which is what the counting of Lemma 4.1 uses.
--
--   **Formalization Note** A circuit lists its vertices in a topological order; every gate carries a scalar on each of its two in-edges, both in-edges may come from one vertex, and a designated vertex is the output. $S$ is the number of $\times$ gates; the size counts all vertices, leaves included.
--
--   Differences from the source:
--
--   - encoding: a path as a sequence of vertices, with "$v_{i+1}=b_i$" for the right branch → a path as a sequence of in-edge choices, the right branch being the right in-edge of the product gate; reason: when the two children of every gate are distinct, as in the source's DAGs, the two notions coincide; with repeated in-edges only the edge reading is true ($x\times x$ has $\mathcal B=\{1,x\}$ and one vertex path)
--   - generalization: fan-in 2 circuits on a directed acyclic graph (two in-edges per gate) → both in-edges of a gate may come from the same vertex; reason: enlarges the class of circuits; every circuit of the source is one of these
--   - encoding: a directed acyclic graph → vertices $0,\dots,s-1$ listed in a topological order, the children of vertex $k$ having index $<k$; reason: every finite DAG has a topological order; the same circuits
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $\mathbb F\langle X\rangle$ → the polynomials of $\mathbb F\langle X,Y\rangle$ in the $X$-variables only; spans are taken inside $\mathbb F\langle X,Y\rangle$; reason: $\mathbb F\langle X\rangle\to\mathbb F\langle X,Y\rangle$ is an injective algebra map, so spans and dimensions agree
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Lemma 3.3, p.6

import Mathlib
import Definitions.Def_NCQuadLB_Circuit_B
import Definitions.Def_NCQuadLB_Circuit_Path

namespace NCQuadLB

/-- **Lemma 3.3** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.6). For every vertex `v` we have
`ℬ_v = {w_π | π is a path from v to a leaf}`, where for a path `π = (v_0, v_1, …, v_m)` with `v_0 = v`
and `v_m` a leaf, `w_π = ∏_{i=0}^m c_{v_i}`, with `c_{v_i} = (â_i)_X` if `v_i = a_i × b_i` is a product
gate and `v_{i+1} = b_i`, and `c_{v_i} = 1` otherwise.

**Formalization Note** Paths are sequences of in-edge choices (`Circuit.Path`): "`v_{i+1} = b_i`" is
"the path takes the right in-edge of the product gate `v_i`". This agrees with the vertex reading on
circuits whose gates have two distinct children; when both in-edges of a gate come from one vertex the
vertex reading is false (`p = x × x` has `ℬ_p = {1, x}` but one vertex path). -/
theorem lemma_3_3 {F : Type*} [Field F] {n : ℕ} (C : Circuit F (Fin n ⊕ Fin n))
    (v : Fin C.size) :
    C.B v = Set.range (fun π : C.Path v => π.weight) := by sorry

end NCQuadLB
