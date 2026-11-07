-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_2_4
-- name    : MatroidSensOracle.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:49.381689+00:00
-- url     : https://prove2.me/theorems/12f4e21f-c65c-4ed2-922b-74c77887d2b7
-- title:
--   Lemma 2.4 (Cauchy–Binet): $\det(AB^T)=\sum_{|S|=r}\det(A_S)\det(B_S)$
-- statement:
--   Let $R$ be a commutative ring and let $A,B$ be $r\times m$ matrices over $R$ with $m\ge r$. Then
--   $$\det(AB^{T})=\sum_{S\subseteq[m],\ |S|=r}\det(A_S)\det(B_S),$$
--   where the sum ranges over the $\binom mr$ subsets $S$ of size $r$ and $A_S$, $B_S$ are the $r\times r$ submatrices of the columns in $S$ (in increasing order).
--
--   Lemma 3.4 encodes common bases of two linear matroids in a determinant through this identity.
--
--   Differences from the source:
--   - generalization: A, B matrices over the field F → A, B over any commutative ring R; reason: the identity holds over every commutative ring; fields are a special case
--   - encoding: A_S, B_S the corresponding submatrices → colSub: the columns of S in increasing order; reason: the same column order for A and B, so det(A_S) det(B_S) is the printed product
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 2.4, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Lemma 2.4 (Cauchy–Binet).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256
0de50841…), p.12 (PDF p.15): "Let A and B be two r × m matrices with m ⩾ r. Then
det(AB^T) = Σ_{S⊆[m], |S|=r} det(A_S) det(B_S), where the sum ranges over all (m choose r) subsets S of
size r, and A_S, B_S denote the corresponding r × r submatrices."

**Formalization Note.** Stated over any commutative ring `R` (the paper uses a field). `A_S` is
`colSub A S`, the columns of `S` in increasing order; the sum runs over the `r`-element subsets
`S ⊆ Fin m`. -/
theorem lemma_2_4 {R : Type*} [CommRing R] {r m : ℕ} (hrm : r ≤ m) (A B : Matrix (Fin r) (Fin m) R) :
    (A * B.transpose).det =
      ∑ S : {S : Finset (Fin m) // S.card = r}, (colSub A S.1 S.2).det * (colSub B S.1 S.2).det := by sorry

end MatroidSensOracle
