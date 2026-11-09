-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_crossed_sum_trace_decomposition
-- name    : OddPermSum.Evaluation.crossed_sum_trace_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:02.14316+00:00
-- url     : https://prove2.me/theorems/c95957c0-54eb-4197-9c5e-e0cbd91e2ad0
-- title:
--   Lemma 3.2 — binary interval trace decomposition
-- statement:
--   Let $A$ be an invertible matrix of order $2^h$ over a characteristic-two commutative ring and $B=A^{-1}$. Form the complete ordered row and column interval trees. Let $\mathcal R$ contain their row-child pairs $(I,J)$ and $\mathcal C$ their column-child pairs $(L,K)$. Then
--
--   $$T(A,B)=\sum_{(I,J)\in\mathcal R}\sum_{(L,K)\in\mathcal C}\operatorname{tr}\big(A[I,K]B[K,J]A[J,L]B[L,I]\big).$$
--
--   The dyadic-size setting is the source's setting after its explicit $A\oplus I$ padding. At order one the split collections and crossed sum are empty. This identity specifies the trace contributions without asserting an operation bound.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: A invertible over a commutative ring → IsUnit (det A), with Mathlib matrix inverse; reason: the equivalence is the standing convention on p. 5; nonzero determinant would not suffice over rings
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 7, Lemma 3.2, Eq. (3.7), including the preceding tree and padding preamble

import Definitions.Def_OddPermSum_Evaluation_crossedSum
import Definitions.Def_OddPermSum_Evaluation_intervalSplits
import Definitions.Def_OddPermSum_Evaluation_dyadicPadding

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 3.2 after the source's dyadic padding; B is the inverse in the preamble. -/
theorem crossed_sum_trace_decomposition {R : Type*} [CommRing R] [CharP R 2]
    (h : ℕ) (A : Matrix (Fin (2^h)) (Fin (2^h)) R) (hA : IsUnit A.det) :
    crossedSum A A⁻¹ =
      ∑ IJ ∈ intervalSplits h, ∑ LK ∈ intervalSplits h,
        splitTrace A A⁻¹ IJ.1 IJ.2 LK.1 LK.2 := by sorry

end OddPermSum.Evaluation
