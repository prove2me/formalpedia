-- Prove2me | Theorems.Thm_NCQuadLB_Supplement_theorem_5_1
-- name    : NCQuadLB.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:47:19.12953+00:00
-- url     : https://prove2.me/theorems/c148ce63-7829-45ea-a200-54e0503506bf
-- title:
--   Theorem 5.1 — full-rank middle coefficient matrix implies circuit size $\Omega(nd)$
-- statement:
--   Let $\mathbb F$ be any field, let $n\ge2$ and $d\ge1$, and set $X=\{x_1,\dots,x_n\}$. Let $f\in\mathbb F\langle X\rangle$ be a noncommutative polynomial of total degree exactly $2d$. Its middle coefficient matrix $M_f^{d,d}$ is indexed by ordered degree-$d$ monomials $m,m'$ and has entry $[mm']f$.
--
--   If $M_f^{d,d}$ has full rank, then every fan-in $2$ noncommutative arithmetic circuit $C$ with edge scalars that computes $f$ satisfies
--
--   $$
--   nd\le 6\,\operatorname{size}(C).
--   $$
--
--   In particular, every such circuit has size $\Omega(nd)$. The constant $6$ is absolute: it is independent of the field, $n$, $d$, $f$, and the circuit.
--
--   **Formalization Note** Total degree is the published `NCFactorClosure607.Circuits.ncDeg`; the section's degree-$2d$ assumption is explicit. Full rank of the square $n^d\times n^d$ matrix is encoded as nonzero determinant. The circuit is the published `NCQuadLB.Circuit`, whose size counts all vertices, including leaves.
--
--   Differences from the source:
--
--   - generalization: circuit size Ω(nd) → the explicit uniform bound nd ≤ 6·size(C) for every admissible field, n, d, f, and C; reason: the analysis invoked from Lemma 4.1 and Theorem 4.2 gives nd ≤ 6·numMul(C') after substitution, while xᵢ ← xᵢ + yᵢ introduces no product gates, so numMul(C') = numMul(C) ≤ size(C)
--   - generalization: a fan-in 2 circuit represented by a directed acyclic graph → both in-edges of a gate may come from the same vertex; reason: this enlarges the class of circuits, and every circuit of the source is included
--   - generalization: the root of the circuit → a designated output vertex, with additional vertices allowed and counted in the size; reason: this enlarges the class of circuits, and the source's rooted circuits are the special case
--   - encoding: a directed acyclic graph → vertices Fin(size) in topological order, with every child index smaller than its gate index; reason: every finite directed acyclic graph has a topological order
--   - encoding: X = {x₁,…,xₙ} and degree-d monomials → the free algebra on Fin n and tuples Fin d → Fin n, with indices starting at 0; reason: this is a renaming of the same ordered noncommuting variables and words
--   - encoding: M_f^{d,d} has full rank → det(M_f^{d,d}) ≠ 0; reason: the matrix is square over a field, so the conditions are equivalent
--   - encoding: f has total degree exactly 2d → ncDeg f = 2*d, stated as an explicit hypothesis; reason: ncDeg is the maximum length of a word with nonzero coefficient, exactly the source's total degree, and the hypothesis is inherited from the paragraph immediately before Theorem 5.1
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453f21da4d8e225baf84bf89c6cd2feb49797548f4efa6c67543940dcd8), §5 and Theorem 5.1, p.8

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_Supplement_middleCoeffMatrix

namespace NCQuadLB

namespace Supplement

/-- **Theorem 5.1** (Shastri–Willumsgaard, *A Quadratic Lower Bound for Noncommutative
Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256
34159453f21da4d8e225baf84bf89c6cd2feb49797548f4efa6c67543940dcd8, p.8). Let
`n ≥ 2`, `d ≥ 1`, and let `f ∈ F⟨X⟩` have total degree exactly `2d`. If the middle
coefficient matrix `M_f^{d,d}` has full rank, then every circuit computing `f` has size
`Ω(nd)`.

**Formalization Note** Exact total degree is the published `ncDeg f = 2*d`. Full rank of
the square `n^d × n^d` matrix is encoded equivalently as nonzero determinant. The source's
`Ω(nd)` is stated with the explicit absolute constant supplied by the analysis invoked in its
proof: `n*d ≤ 6*C.size`, uniformly over the field, parameters, polynomial, and circuit.
Circuits are the published `NCQuadLB.Circuit`: vertices are topologically ordered, every
in-edge carries a scalar, both in-edges may come from the same vertex, and `size` counts all
vertices, including leaves. -/
theorem theorem_5_1 {F : Type*} [Field F] (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (f : FreeAlgebra F (Fin n))
    (hdeg : NCFactorClosure607.Circuits.ncDeg f = 2 * d)
    (hfull : Matrix.det (middleCoeffMatrix d f) ≠ 0)
    (C : Circuit F (Fin n)) (hC : C.Computes f) :
    n * d ≤ 6 * C.size := by sorry

end Supplement

end NCQuadLB
