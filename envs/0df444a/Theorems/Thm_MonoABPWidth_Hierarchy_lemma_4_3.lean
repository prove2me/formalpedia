-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_3
-- name    : MonoABPWidth.Hierarchy.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:14.256262+00:00
-- url     : https://prove2.me/theorems/4c6b3874-6001-4bdd-80e4-9fb6cd35722f
-- title:
--   Lemma 4.3 — width-two completion at depth n
-- statement:
--   Let $k,n\ge1$ and let $A$ be any mABP of width at most two, with output $f$ supported inside $\operatorname{imm}_{k,n}$. There is an mABP $B$ of width at most two and depth exactly $n$, with monotone output $f'$, such that
--   $$
--   \operatorname{supp}(f)\subseteq\operatorname{supp}(f')\subseteq\operatorname{supp}(\operatorname{imm}_{k,n}).
--   $$
--   No restriction is imposed on the depth or simplicity of $A$, and $f=0$ is allowed. The conclusion is support completion rather than equality of coefficients or polynomials. It gives the full width-two endpoint needed by the main lower bound.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: the (1,1) entry of a k-by-k matrix product → k ≥ 1; reason: the source entry is defined only in positive matrix dimension; no defined instance is excluded
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
--   - encoding: a monotone polynomial f computed by a width-bounded mABP → f is the computed path-sum A.output of the actual finite mABP; reason: nonnegative affine labels imply nonnegative output coefficients; no polynomial instance is excluded
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma 4.3, p. 7, PDF 8

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Lemma 4.3, p.7 / PDF8: both inclusions, exact depth n, and zero output retained. -/
theorem lemma_4_3 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ 2)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    ∃ B : MABP (SetMultCost.IMMVar k n),
      MonotonePolynomial B.output ∧ B.width ≤ 2 ∧ B.depth = n ∧
      A.output.support ⊆ B.output.support ∧ B.output.support ⊆ (SetMultCost.imm ℝ k n).support := by sorry

end MonoABPWidth.Hierarchy
