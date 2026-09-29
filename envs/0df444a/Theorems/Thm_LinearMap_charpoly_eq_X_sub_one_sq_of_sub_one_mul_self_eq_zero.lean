-- Prove2me | Theorems.Thm_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero
-- name    : LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/98cc4bb1-5bb7-55e7-842a-464e09383177
-- title:
--   Rank-two unipotent endomorphism has charpoly (X-1)²
-- statement:
--   Let $A$ be a commutative ring which is an integral domain, and let $V$ be an $A$-module which is free and finite (finitely generated) over $A$, with $\operatorname{finrank}_A V = 2$. Let $f$ be an $A$-linear endomorphism of $V$ satisfying the operator identity $(f-1)(f-1) = 0$ in the ring $\operatorname{End}_A(V)$, where $1$ denotes the identity endomorphism and the product is composition. The conclusion is an identity in the polynomial ring $A[X]$: the characteristic polynomial $\operatorname{charpoly} f$, defined for an endomorphism of a finite free module as the characteristic polynomial of its matrix in any basis, equals $(X-1)^2$. Both the domain hypothesis on $A$ and the rank hypothesis are genuinely used: over a ring with nilpotents the nilpotence of $f-1$ does not by itself force the characteristic polynomial to be $(X-1)^2$.
--
--   This is the elementary linear-algebra fact that a unipotent endomorphism of a rank-two free module over a domain has characteristic polynomial $(X-1)^2$. It is used to convert the operator identity $(\sigma-1)^2=0$ on a two-dimensional Tate module into the characteristic-polynomial form of unipotence on inertia, and is cited by [`GaloisRepAdic.isUnipotentOnInertiaAt_of_isPrimitiveForm_of_dvd_of_not_sq_dvd`](thm.html#GaloisRepAdic.isUnipotentOnInertiaAt_of_isPrimitiveForm_of_dvd_of_not_sq_dvd) and [`GaloisRepAdic.isUnipotentOnInertiaAt_of_tateModule_quotient`](thm.html#GaloisRepAdic.isUnipotentOnInertiaAt_of_tateModule_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero.lean

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero {A : Type u} [CommRing A]
    [IsDomain A] {V : Type v} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 2) (f : Module.End A V) (hf : (f - 1) * (f - 1) = 0) :
    LinearMap.charpoly f = (Polynomial.X - 1) ^ 2 := by sorry
