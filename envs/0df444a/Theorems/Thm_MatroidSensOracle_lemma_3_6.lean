-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_3_6
-- name    : MatroidSensOracle.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:49.315822+00:00
-- url     : https://prove2.me/theorems/68f37713-92a1-4da1-b358-5e86295b5615
-- title:
--   Lemma 3.6 (Representation of $k$-fold union [75]): $A^{\vee k}=(AD_1;\dots;AD_k)$ represents $M^{\vee k}$ with probability $\ge1-|S|/|\mathbb F|$
-- statement:
--   Let $\mathbb F$ be a finite field, $A\in\mathbb F^{N\times m}$ represent a matroid $M$, and $k\ge0$. For diagonal matrices $D_1,\dots,D_k$ with independent uniform diagonal entries, let $A^{\vee k}$ be the $kN\times m$ matrix stacking $AD_1,\dots,AD_k$.
--
--   1. For every fixed $S$ independent in the $k$-fold union $M^{\vee k}$, the columns $(A^{\vee k})_S$ are linearly independent with probability at least $1-|S|/|\mathbb F|$.
--   2. For every $S$ dependent in $M^{\vee k}$, the columns $(A^{\vee k})_S$ are linearly dependent for every choice of $D_1,\dots,D_k$.
--
--   It reduces $k$-intersection-packing to common bases (Theorem 3.7).
--
--   Differences from the source:
--   - encoding: A^{∨k} = (AD_1; …; AD_k) ∈ F^{kN×m} → rows indexed by (block i, row r); the diagonals as D : Fin k → Fin m → F, uniform; reason: row order does not affect column ranks
--   - encoding: sampled uniformly at random from F → F a finite field; probability = fraction of D ∈ F^{k×m}; reason: uniform sampling needs a finite field, as in the paper (p.13)
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 3.6, p.20 (PDF p.23), citing Narayanan, Saran and Vazirani [75]

import Mathlib
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle

open Classical in
/-- **Lemma 3.6 (Representation of k-Fold Union [75]).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.20 (PDF p.23): "Let A ∈ F^{N×m} be a linear representation of a
matroid M = (E, ℐ) over a field F. For each i ∈ [k], let D_i ∈ F^{m×m} be a diagonal matrix whose
diagonal entries are sampled independently and uniformly at random from F. Define the block matrix
A^{∨k} = (AD_1; …; AD_k) ∈ F^{kN×m}. Then A^{∨k} satisfies the following properties:
1. For any fixed set S ∈ ℐ^{∨k}, the column submatrix (A^{∨k})_S has full column rank with probability
at least 1 − |S|/|F|.
2. For any dependent set S ∉ ℐ^{∨k}, the columns (A^{∨k})_S are linearly dependent for all choices of
{D_i}_{i=1}^k."

**Formalization Note.** `F` is a finite field (the sampling is uniform). The diagonals are
`D : Fin k → Fin m → F`, uniform over `F^{k×m}`; `unionRep A D` indexes the rows of `A^{∨k}` by
(block, row), which does not change column ranks. `ℐ^{∨k}` is `UnionIndep A k`: the sets splitting
into `k` disjoint independent sets. -/
theorem lemma_3_6 {F : Type} [Field F] [Fintype F] [DecidableEq F] {N m : ℕ}
    (A : Matrix (Fin N) (Fin m) F) (k : ℕ) :
    (∀ S : Finset (Fin m), UnionIndep A k S →
      1 - (S.card : ℝ) / Fintype.card F ≤
        ((Finset.univ.filter fun D : Fin k → Fin m → F => ColIndep (unionRep A D) S).card : ℝ) /
          Fintype.card (Fin k → Fin m → F)) ∧
    (∀ S : Finset (Fin m), ¬ UnionIndep A k S →
      ∀ D : Fin k → Fin m → F, ¬ ColIndep (unionRep A D) S) := by sorry

end MatroidSensOracle
