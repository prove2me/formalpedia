-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_equal_row_identity
-- name    : OddPermSum.Evaluation.equal_row_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:17:53.320397+00:00
-- url     : https://prove2.me/theorems/3ccadaf9-5419-47e3-aae7-b0468ae6e900
-- title:
--   Lemma 4.1 — scaled equal-row evaluation
-- statement:
--   Let $A$ be invertible over a commutative ring of characteristic two, put $B=A^{-1}$ and $\Delta=\det A$, and let $p\ne q$ be row indices. For every scalar $t$, let $N$ replace row $q$ of $A$ by $t$ times row $p$. Then
--
--   $$\Phi(N)=t\Delta\sum_j A_{p,j}^{\,2}B_{j,p}B_{j,q}.$$
--
--   The statement allows zero divisors in the coefficient ring and arbitrary $t$, including zero. Only the determinant's being a unit is required. This supplies the off-diagonal row-replacement values underlying the full-gradient formula.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: A invertible over a commutative ring → IsUnit (det A), with Mathlib matrix inverse; reason: the equivalence is the standing convention on p. 5; nonzero determinant would not suffice over rings
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 10, Lemma 4.1, Eq. (4.1), proof continues on p. 11

import Definitions.Def_OddPermSum_Evaluation_phi

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 4.1 over commutative rings; inverse existence means a unit determinant. -/
theorem equal_row_identity {R : Type*} [CommRing R] [CharP R 2]
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (p q : Fin n) (hpq : p ≠ q) (t : R) :
    phi (fun i j => if i = q then t * A p j else A i j) =
      t * A.det * ∑ j, (A p j)^2 * A⁻¹ j p * A⁻¹ j q := by sorry

end OddPermSum.Evaluation
