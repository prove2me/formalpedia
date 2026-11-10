-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_4
-- name    : MonoABPWidth.Hierarchy.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:25.839313+00:00
-- url     : https://prove2.me/theorems/b91a5a6b-5b2a-4655-a176-0c95d03d5b19
-- title:
--   Lemma A.4 — edge labels have a single term
-- statement:
--   Let $k,n\ge1$. Let $A$ be an mABP in the variables of $n$ symbolic $k\times k$ matrices, satisfying relevance, and assume its output is supported inside the $(1,1)$ entry of their product. Then
--   $$
--   \text{every edge label is a nonnegative constant or a nonnegative multiple of one variable.}
--   $$
--   The input model still permits full nonnegative affine forms. The assertion is a conclusion about their actual labels, providing property 3 of Definition A.1.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: the (1,1) entry of a k-by-k matrix product → k ≥ 1; reason: the source entry is defined only in positive matrix dimension; no defined instance is excluded
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
--   - encoding: a monotone polynomial f computed by a width-bounded mABP → f is the computed path-sum A.output of the actual finite mABP; reason: nonnegative affine labels imply nonnegative output coefficients; no polynomial instance is excluded
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma A.4, p. 28, PDF 29

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Lemma A.4, p.28 / PDF29. Positive matrix-chain length is the source convention;
all nonnegative affine labels are allowed in the input. -/
theorem lemma_A_4 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hrel : A.Relevant)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    A.SingleTermEdges := by sorry

end MonoABPWidth.Hierarchy
