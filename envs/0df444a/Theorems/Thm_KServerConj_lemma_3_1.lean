-- Prove2me | Theorems.Thm_KServerConj_lemma_3_1
-- name    : KServerConj.lemma_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:49:05.403814+00:00
-- url     : https://prove2.me/theorems/85c773ac-c024-41ea-8e8c-0044025d9916
-- title:
--   Lemma 3.1 — Schläfli: $\det(\mathrm{Sym}^2A)=(\det A)^{k+1}$
-- statement:
--   For every $k\times k$ matrix $A$ over a commutative ring, the matrix of the induced map $\mathrm{Sym}^2A$ on quadratic forms, in the monomial basis $(e_ie_j)_{i\le j}$, satisfies
--
--   $$\det(\mathrm{Sym}^2A)=(\det A)^{k+1}.$$
--
--   The exponent $k+1$ counts how often a basis vector occurs among the products $e_ie_j$: twice in its square and once in each of its $k-1$ mixed products. It is the source of the factor $k+1$ in the terminal bound of the potential (Lemma 5.1), and it shows that $\Psi$ is unchanged by a normalization with $\det B=1$.
--
--   Differences from the source:
--   - generalization: every invertible k × k matrix A over K → every k × k matrix over every commutative ring; reason: the identity is a polynomial identity with integer coefficients in the entries of A; the invertible case over K is a special case
--   - encoding: the monomial basis (e_ie_j)_{1≤i≤j≤k} in lexicographic order → rows and columns indexed by Sym2 (Fin k); reason: a determinant is unchanged by the same reordering of rows and columns
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 3.1, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_KServerConj_symProd

namespace KServerConj

/-- **Lemma 3.1 (Schläfli).** Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*,
arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.9 (PDF p.10): "For every
invertible k × k matrix A, det(Sym² A) = (det A)^{k+1}. (15)"

**Formalization Note.** `sym2Mat A` is the matrix of `Sym² A` in the monomial basis
`(e_ie_j)_{i≤j}`, indexed by `Sym2 (Fin k)`. The identity is stated for every square matrix over
every commutative ring: it is a polynomial identity in the entries of `A`, so the invertible case
over the paper's field `K` is a special case. -/
theorem lemma_3_1 {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (sym2Mat A).det = A.det ^ (k + 1) := by sorry

end KServerConj
