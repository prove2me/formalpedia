-- Prove2me | Theorems.Thm_IntQuotHNP_lattice_6_basis
-- name    : IntQuotHNP.lattice_6_basis
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:54:03.865489+00:00
-- url     : https://prove2.me/theorems/62cb7e64-2f0b-4fa3-9dda-c761f2e74d77
-- title:
--   §4.1, eq. (6) — the rows of (6) are linearly independent, $k=N$, $m=d=N(N+1)/2$
-- statement:
--   On every promised MIHNP input, the $m$ rows of the basis matrix (6), namely the scaled coefficient vectors $\Phi(P_{ij})$ for $i<j$ and $\Phi(px_h)$, are linearly independent over $\mathbb R$ in $\mathbb R^d$, with
--   $$
--   m=d=\binom N2+N=\frac{N(N+1)}2 .
--   $$
--   This makes (6) a genuine basis of a full-rank lattice of $\mathbb R^d$, a requirement of the common recovery framework.
--
--   Differences from the source:
--   - encoding: rows listed as P_ij, then px_2, …, px_N, px_1, and k = N → rows and coordinates indexed by the type Mon N; the k = N error variables are the index type Fin N; reason: a row order does not affect linear independence, and the types carry the counts
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, p.22 (PDF p.23); eq. (6), p.23 (PDF p.24)

import Mathlib
import Definitions.Def_IntQuotHNP_MIHNPInput
import Definitions.Def_IntQuotHNP_MIHNPLattice

namespace IntQuotHNP

/-- **The rows of (6) are linearly independent, `k = N`, `m = d = N(N + 1)/2`** (§4.1).
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §4.1, pp.22–23 (PDF pp.23–24): "Thus the nonconstant coefficient vectors Φ(P_i) from
Definition 2.3 are linearly independent, with k = N, m = d = (N choose 2) + N = N(N + 1)/2."

On every promised MIHNP input the `m` rows of the basis matrix (6), the scaled coefficient vectors
`Φ(P_ij)` (`i < j`) and `Φ(p x_h)`, are linearly independent over `ℝ` in `ℝ^d`, and
`m = d = N(N + 1)/2`.

**Formalization Note.** Rows and coordinates are both indexed by `Mon N`, so `m = d = |Mon N|`; the
`k = N` error variables are the coordinates of `Fin N`. -/
theorem lattice_6_basis (I : MIHNPInput) (hI : IsPromised I) :
    LinearIndependent ℝ (latticeBasis I) ∧ Fintype.card (Mon I.N) = I.N * (I.N + 1) / 2 := by sorry

end IntQuotHNP
