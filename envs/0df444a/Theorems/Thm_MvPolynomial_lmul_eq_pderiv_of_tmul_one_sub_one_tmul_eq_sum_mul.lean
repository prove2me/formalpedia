-- Prove2me | Theorems.Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
-- name    : MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/ebbbc7d4-a3e3-550a-b1c2-07bfe0a8aab1
-- title:
--   Bézout coefficients multiply down to partial derivatives
-- statement:
--   Let $R$ be a commutative ring, let $m$ be a natural number, and write $P = R[x_0,\dots,x_{m-1}]$ for the polynomial ring `MvPolynomial (Fin m) R`. Let $g \in P$ and let $a : \mathrm{Fin}\,m \to P \otimes_R P$ be a family of elements of the tensor square of $P$ over $R$, subject to the single hypothesis that in $P \otimes_R P$ one has the identity $$g \otimes 1 - 1 \otimes g = \sum_{j} a_j \cdot (x_j \otimes 1 - 1 \otimes x_j),$$ the sum being over all $j \in \mathrm{Fin}\,m$ and the product being that of the $R$-algebra $P \otimes_R P$. Then for each index $j$ the image of $a_j$ under the multiplication map $P \otimes_R P \to P$, $u \otimes v \mapsto uv$ (namely `Algebra.TensorProduct.lmul' R`), equals the partial derivative $\partial g/\partial x_j$, that is, `MvPolynomial.pderiv j g`. No assumption is made on the family $a$ beyond the displayed identity; the conclusion holds for any choice of such Bézout coefficients, even though the $a_j$ themselves are not determined by $g$.
--
--   This is the statement that an arbitrary family of Bézout coefficients expressing $g \otimes 1 - 1 \otimes g$ in terms of the generators $x_j \otimes 1 - 1 \otimes x_j$ of the diagonal ideal represents, after multiplying down, the differential $dg = \sum_j (\partial g/\partial x_j)\,dx_j$ in $I_\Delta/I_\Delta^2 \cong \Omega_{P/R}$. It is used in the computation [`Algebra.lmul_bezoutian_eq_jacobianDet`](thm.html#Algebra.lmul_bezoutian_eq_jacobianDet), which identifies the image of a Bezoutian under multiplication with a Jacobian determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g := by sorry
