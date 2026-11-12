-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_5
-- name    : MonoABPWidth.Hierarchy.lemma_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:14.767427+00:00
-- url     : https://prove2.me/theorems/f5467c22-89f7-42a2-94b2-e3793dd1e15f
-- title:
--   Lemma 4.5 — width decomposition (corrected: depth-one count)
-- statement:
--   Let $n\ge1$ and $3\le w<k$. Let $A$ be an mABP of width at most $w$ and depth $d$, whose output $f=f^{(A)}$ satisfies
--   $$
--   \operatorname{supp}(f)\subseteq\operatorname{supp}(\operatorname{imm}_{k,n}),\qquad
--   |\operatorname{supp}(f)|>\frac wk|\operatorname{supp}(\operatorname{imm}_{k,n})|.
--   $$
--   There are $r$ mABPs $B_j$, of width at most $w-1$ and depth at most $d$, and positive real coefficients $c_j$, such that
--   $$
--   f=\sum_{j=1}^r c_j f^{(B_j)},\qquad r\le d^2,\qquad d\ge2\Longrightarrow r<d^2,\qquad
--   \operatorname{supp}(f^{(B_j)})\subseteq\operatorname{supp}(f)\quad(1\le j\le r).
--   $$
--   Here $|\operatorname{supp}(\operatorname{imm}_{k,n})|=k^{n-1}$; using the fraction form also keeps the $n=1$ threshold $w/k$ literal. The decomposition supplies the smaller-width outputs used by the main result. The positive coefficients and output-support containment are the extra conclusions furnished by the displayed decomposition on p.9, after discarding zero coefficients.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - correction: r < d² at every depth → r ≤ d², retaining r < d² whenever d ≥ 2; reason: w=3, k=4, n=1 and one edge labelled x^(1)_(1,1) satisfy every printed hypothesis with d=1 and support density 1>3/4; r<1 would force a zero sum
--   - generalization: a real linear combination of smaller-width outputs → positive retained coefficients and each retained output supported inside supp(f); reason: the displayed nonnegative path-constant decomposition on p.9, lines298–300, yields these conclusions after deleting zero coefficients; forgetting them recovers the corrected source statement
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
--   - encoding: a monotone polynomial f computed by a width-bounded mABP → f is the computed path-sum A.output of the actual finite mABP; reason: nonnegative affine labels imply nonnegative output coefficients; no polynomial instance is excluded
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma 4.5; displayed decomposition lines298–300 on p.9, PDF10, p. 8, PDF 9

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

open scoped BigOperators

namespace MonoABPWidth.Hierarchy

/-- Lemma 4.5, p.8 / PDF9, corrected only at depth one: r ≤ d² and r < d² for d ≥ 2.
Counterexample to the printed strict count: w=3, k=4, n=1, a single variable edge, d=1.
The p.9 / PDF10 displayed decomposition additionally yields positive retained coefficients
and support containment; these are conclusions, not assumptions. -/
theorem lemma_4_5 (k n w : ℕ) (hn : 0 < n) (hw : 3 ≤ w) (hwk : w < k)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ w)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support)
    (hdense : (w : ℝ) / (k : ℝ) * ((SetMultCost.imm ℝ k n).support.card : ℝ) <
      (A.output.support.card : ℝ)) :
    ∃ (r : ℕ) (B : Fin r → MABP (SetMultCost.IMMVar k n)) (c : Fin r → ℝ),
      r ≤ A.depth ^ 2 ∧ (2 ≤ A.depth → r < A.depth ^ 2) ∧
      (∀ j : Fin r, 0 < c j ∧ (B j).width ≤ w - 1 ∧ (B j).depth ≤ A.depth ∧
        (B j).output.support ⊆ A.output.support) ∧
      A.output = ∑ j : Fin r, MvPolynomial.C (c j) * (B j).output := by sorry

end MonoABPWidth.Hierarchy
