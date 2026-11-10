-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_theorem_4_8
-- name    : MonoABPWidth.Hierarchy.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:07.589387+00:00
-- url     : https://prove2.me/theorems/5e891cf0-4b44-4f0a-b0f8-9d3f5da427c9
-- title:
--   Theorem 4.8 — exact depth lower bound for bounded-width monotone ABPs
-- statement:
--   Let $n\ge1$ and $3\le w<k$ be integers. Let $A$ be any real monotone algebraic branching program of width at most $w$, and put $f=f^{(A)}$, $d=\operatorname{depth}(A)$. If $f$ has exactly the support of $\operatorname{imm}_{k,n}$, then
--   $$
--   d\ge\left(\frac{k}{w-1}\right)^{\frac12\left\lfloor n^{1/(w-2)}\right\rfloor-1}.
--   $$
--   The exponent is half of the floor, minus one. All positive lengths are covered, including $n=1$ and non-perfect powers. Nonzero coefficients on the full support are arbitrary nonnegative reals, with no requirement of coefficient equality with IMM. Input labels may be arbitrary nonnegative affine sums and the program may use any variable order. Simplicity, homogeneity, decomposition witnesses, and projections are not input assumptions. This is the exact finite depth bound underlying the width hierarchy.
--
--   **Formalization Note** The quotient, root, division by two, and subtraction in the exponent are real operations. The natural floor agrees with the integer floor because the root is positive.
--
--   Differences from the source:
--   - reading: matrix-chain length n ∈ ℕ, without an empty-chain convention → n ≥ 1 (and m ≥ 1 for divisors); reason: the paper specifies n matrices and k^(n−1) monomials (pp.4,10); an empty product and a depth-zero program would falsify the goal
--   - encoding: the (1,1) entry of a k-by-k matrix product → k ≥ 1; reason: the source entry is defined only in positive matrix dimension; no defined instance is excluded
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
--   - encoding: a monotone polynomial f computed by a width-bounded mABP → f is the computed path-sum A.output of the actual finite mABP; reason: nonnegative affine labels imply nonnegative output coefficients; no polynomial instance is excluded
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Theorem 4.8, p. 11, PDF 12

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

namespace MonoABPWidth.Hierarchy

/-- Theorem 4.8, p.11 / PDF12: exact support-based depth bound.
Every positive n, including n=1 and non-perfect powers. The exponent is half
the floor, minus one, in ℝ. No simplicity, projection or coefficient-equality assumption. -/
theorem theorem_4_8 (k n w : ℕ) (hn : 0 < n) (hw : 3 ≤ w) (hwk : w < k)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ w)
    (hsupport : A.output.support = (SetMultCost.imm ℝ k n).support) :
    Real.rpow ((k : ℝ) / ((w : ℝ) - 1))
      (((Nat.floor (Real.rpow (n : ℝ) (1 / ((w : ℝ) - 2))) : ℝ) / 2) - 1) ≤
        (A.depth : ℝ) := by sorry

end MonoABPWidth.Hierarchy
