-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_invertible_gradient_formula
-- name    : OddPermSum.Evaluation.invertible_gradient_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:21:49.440673+00:00
-- url     : https://prove2.me/theorems/f38bd912-0cb6-4c85-8718-0f96daef2047
-- title:
--   Proposition 4.2 — full transposed gradient formula
-- statement:
--   Let $A$ be invertible over a commutative ring of characteristic two, set $B=A^{-1}$ and $\Delta=\det A$, and define $C_{p,j}=A_{p,j}^2B_{j,p}$. Then the entire transposed formal gradient satisfies
--
--   $$G(A)=\Delta BCB+(\Phi(A)+\Delta)B.$$
--
--   The products $BCB$ are matrix products, and the other factors are scalars. This identity is over commutative rings, including rings with zero divisors, with unit determinant as the precise invertibility condition. It is the formula for all columns simultaneously, with the transpose convention fixed by $G(A)_{j,i}=\partial\Phi/\partial A_{i,j}$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: A invertible over a commutative ring → IsUnit (det A), with Mathlib matrix inverse; reason: the equivalence is the standing convention on p. 5; nonzero determinant would not suffice over rings
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 11, Proposition 4.2, Eq. (4.4), proof continues on p. 12

import Definitions.Def_OddPermSum_Evaluation_gradient
import Definitions.Def_OddPermSum_Evaluation_gradientCoefficient

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Proposition 4.2. Products are matrix products and scalar factors act entrywise. -/
theorem invertible_gradient_formula {R : Type*} [CommRing R] [CharP R 2]
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) :
    gradient A = A.det • (A⁻¹ * gradientCoefficient A A⁻¹ * A⁻¹) +
      (phi A + A.det) • A⁻¹ := by sorry

end OddPermSum.Evaluation
