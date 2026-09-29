-- Prove2me | Theorems.Thm_HopfAlgebra_finiteFlat_tensorProduct
-- name    : HopfAlgebra.finiteFlat_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/8ddce2a8-8f57-5751-a3b2-4a7a60298a2b
-- title:
--   Tensor product of finite flat Hopf algebras is finite flat
-- statement:
--   Let $R$ be a commutative ring and let $A$ and $B$ be commutative rings equipped with Hopf algebra structures over $R$ (in particular each is an $R$-algebra, hence an $R$-module). Assume that $A$ is finite and flat as an $R$-module and that $B$ is finite and flat as an $R$-module. The assertion is that the $R$-module tensor product $A \otimes_R B$ is again finite, i.e. finitely generated, and flat over $R$; the two statements are packaged as a conjunction. Note that the conclusion concerns only the $R$-module $A \otimes_R B$: no Hopf algebra, coalgebra or algebra structure on the tensor product is asserted or constructed, and the Hopf algebra hypotheses on $A$ and $B$ enter only in so far as they supply the underlying $R$-module structures. Thus the statement is the module-theoretic shadow of the classical fact that a finite product of affine finite flat group schemes over $R$ is again affine finite flat.
--
--   Classically this is the closure of the category of finite flat commutative group schemes over $R$ under finite products, $\operatorname{Spec}(A \otimes_R B) = \operatorname{Spec} A \times_{\operatorname{Spec} R} \operatorname{Spec} B$. Within this development it is the tensor-product step used by [`HopfAlgebra.exists_finiteFlat_pi`](thm.html#HopfAlgebra.exists_finiteFlat_pi), where a finite power of a representation admitting a finite flat prolongation is given one by a tensor power of the corresponding Hopf algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finiteFlat_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfAlgebra.finiteFlat_tensorProduct {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B] :
    Module.Finite R (A ⊗[R] B) ∧ Module.Flat R (A ⊗[R] B) := by sorry
