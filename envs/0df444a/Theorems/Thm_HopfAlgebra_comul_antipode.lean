-- Prove2me | Theorems.Thm_HopfAlgebra_comul_antipode
-- name    : HopfAlgebra.comul_antipode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/8ef2a549-7689-5b5e-a6fb-bea68b0b34ed
-- title:
--   The antipode is a coalgebra anti-morphism
-- statement:
--   Let $R$ be a commutative semiring, let $A$ be a semiring carrying a Hopf algebra structure over $R$ (so $A$ is an $R$-bialgebra with comultiplication $\Delta =$ `Coalgebra.comul`, counit, and antipode $S =$ `HopfAlgebra.antipode R`), and let $a \in A$. The assertion is the identity in $A \otimes_R A$
--   $$\Delta(S(a)) \;=\; \tau\bigl((S \otimes S)(\Delta(a))\bigr),$$
--   where $S \otimes S$ is the $R$-linear map `TensorProduct.map` of $S$ with itself and $\tau$ is the flip isomorphism `TensorProduct.comm R A A` of $A \otimes_R A$, applied to the element $(S \otimes S)(\Delta(a))$. In Sweedler notation, $\Delta(S a) = \sum S(a_{(2)}) \otimes S(a_{(1)})$. No commutativity of $A$ and no cocommutativity of its coalgebra structure is assumed; the statement is pointwise in $a$, the underlying identity of $R$-linear maps $A \to A \otimes_R A$ being obtained by evaluating at each $a$.
--
--   This is the comultiplication half of the classical statement that the antipode of a Hopf algebra is an anti-morphism of bialgebras (Sweedler, Proposition 4.0.1), the anti-multiplicativity and counit halves being available in Mathlib. It is used to deduce that for a cocommutative Hopf algebra the antipode commutes with comultiplication, in [`HopfAlgebra.map_antipode_comul_of_isCocomm`](thm.html#HopfAlgebra.map_antipode_comul_of_isCocomm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_comul_antipode.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.comul_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
            (Coalgebra.comul a)) := by sorry
