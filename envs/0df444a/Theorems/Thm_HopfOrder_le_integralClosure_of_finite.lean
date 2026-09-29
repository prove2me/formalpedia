-- Prove2me | Theorems.Thm_HopfOrder_le_integralClosure_of_finite
-- name    : HopfOrder.le_integralClosure_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/1bd017d9-f382-54a1-a8a3-40e87c36a658
-- title:
--   A module-finite subalgebra lies in the integral closure
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative ring equipped with an $R$-algebra structure, and let $S$ be an $R$-subalgebra of $A$ which is finite as an $R$-module. Then $S$, viewed as a subalgebra of $A$, is contained in the integral closure of $R$ in $A$, that is, in the subalgebra `integralClosure R A` of those elements of $A$ that are integral over $R$: every element of $S$ satisfies a monic polynomial with coefficients in $R$. The containment is stated as an inequality of subalgebras of $A$, so it is exactly the assertion that each $x \in S$ lies in `integralClosure R A`. No hypothesis beyond module-finiteness of $S$ over $R$ (and the commutativity of $R$ and $A$) is imposed; in particular $R$ need not be Noetherian, a domain, or inject into $A$.
--
--   This is the elementary implication "module-finite $\Rightarrow$ integral" in the form needed for subalgebras: the $R$-algebra of a module-finite subalgebra is contained in the integral closure of $R$. It is used in the treatment of orders and Hopf orders, being cited by [`HopfOrder.exists_isGreatest`](thm.html#HopfOrder.exists_isGreatest) and by [`Subalgebra.eq_integralClosure_of_etale_of_span_eq_top`](thm.html#Subalgebra.eq_integralClosure_of_etale_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_le_integralClosure_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u w

theorem HopfOrder.le_integralClosure_of_finite
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by sorry
