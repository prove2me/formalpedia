-- Prove2me | Theorems.Thm_GeomDL_Sets_eq_6_invariant
-- name    : GeomDL.Sets.eq_6_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:10.010023+00:00
-- url     : https://prove2.me/theorems/2a7ad02e-2a5d-49b8-92cd-f92953ec4c9b
-- title:
--   §4.1, eq. (6), p. 32 — the sum readout φ(Σᵤ ψ(xᵤ)) is permutation invariant
-- statement:
--   Let $\mathbf X\in\mathbb R^{n\times d}$ have rows $\mathbf x_1,\dots,\mathbf x_n$, let $\psi:\mathbb R^d\to M$ take values in a commutative additive monoid $M$, and let $\phi:M\to Y$ be arbitrary. Define
--
--   $$f(\mathbf X)=\phi\Big(\sum_{u\in\mathcal V}\psi(\mathbf x_u)\Big).$$
--
--   Then $f$ is permutation invariant: $f(\mathbf P\mathbf X)=f(\mathbf X)$ for every $n\times n$ permutation matrix $\mathbf P$.
--
--   This is the book's first example of a permutation-invariant function on sets, the readout of Deep Sets.
--
--   **Formalization Note** $\mathbf P\mathbf X$ reorders the rows of $\mathbf X$, row $u$ of $\mathbf P\mathbf X$ being row $\sigma^{-1}(u)$ of $\mathbf X$; the statement quantifies over all $\sigma\in\Sigma_n$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eq. (6), p. 32

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §4.1, eq. (6), p. 32: `f(X) = φ(∑_{u ∈ V} ψ(x_u))` is permutation invariant,
`f(PX) = f(X)` for every permutation matrix `P` (rows of `PX` reordered by `σ⁻¹`). -/
theorem eq_6_invariant {n d : ℕ} {M Y : Type*} [AddCommMonoid M] (φ : M → Y)
    (ψ : (Fin d → ℝ) → M) :
    IsPermInvariant (sumReadout φ ψ : Matrix (Fin n) (Fin d) ℝ → Y) := by sorry

end GeomDL.Sets
