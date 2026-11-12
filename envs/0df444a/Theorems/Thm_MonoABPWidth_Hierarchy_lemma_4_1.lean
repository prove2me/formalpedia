-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_1
-- name    : MonoABPWidth.Hierarchy.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:12.866857+00:00
-- url     : https://prove2.me/theorems/6f6ee258-a19a-4a14-a9d6-40f269915f7b
-- title:
--   Lemma 4.1 — polynomial-preserving simplification
-- statement:
--   Let $k,n\ge1$ and let $A$ be an mABP of width $w$ and depth $d$, with nonzero output supported inside $\operatorname{supp}(\operatorname{imm}_{k,n})$. There is a simple mABP $B$ such that
--   $$
--   f^{(B)}=f^{(A)},\qquad \operatorname{width}(B)\le w,\qquad \operatorname{depth}(B)\le d.
--   $$
--   All three simplicity conditions are obtained: nonzero prefixes and suffixes, separate pairwise nonproportionality, and single-term labels. Polynomial equality, rather than only support equality, is preserved.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: the (1,1) entry of a k-by-k matrix product → k ≥ 1; reason: the source entry is defined only in positive matrix dimension; no defined instance is excluded
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
--   - encoding: a monotone polynomial f computed by a width-bounded mABP → f is the computed path-sum A.output of the actual finite mABP; reason: nonnegative affine labels imply nonnegative output coefficients; no polynomial instance is excluded
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma 4.1, p. 6, PDF 7

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Lemma 4.1, p.6 / PDF7: polynomial-preserving simplification at no width or depth cost. -/
theorem lemma_4_1 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hzero : A.output ≠ 0)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    ∃ B : MABP (SetMultCost.IMMVar k n),
      B.width ≤ A.width ∧ B.depth ≤ A.depth ∧ B.Simple ∧ B.output = A.output := by sorry

end MonoABPWidth.Hierarchy
