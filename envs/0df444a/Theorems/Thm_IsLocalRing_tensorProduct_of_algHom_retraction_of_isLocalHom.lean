-- Prove2me | Theorems.Thm_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom
-- name    : IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/bf421381-72e6-5712-97da-7bdb60f46095
-- title:
--   Base change O⊗_R A of a finite augmented local algebra is local
-- statement:
--   Let $R$ be a commutative local ring; let $A$ be a commutative $R$-algebra which is itself a local ring and is finite as an $R$-module; let $\varepsilon \colon A \to R$ be a homomorphism of $R$-algebras (so an augmentation splitting the structure map $R \to A$); and let $O$ be a commutative local $R$-algebra whose structure map $\operatorname{algebraMap} R O$ is a local homomorphism, i.e. carries non-units to non-units. Then the tensor product $O \otimes_R A$, with its ring structure, is again a local ring: it is nontrivial and for every $x \in O \otimes_R A$ either $x$ or $1 - x$ is a unit. No flatness, Noetherian or Artinian hypothesis is imposed on $R$, $A$ or $O$, and the maximal ideal of the tensor product is not named in the statement (classically it is the kernel of $O \otimes_R A \to O \to O/\mathfrak m_O$, $o \otimes a \mapsto o\,\varepsilon(a)$).
--
--   This is the commutative-algebra fact that base change of a module-finite local $R$-algebra with an augmentation along a local homomorphism of local rings stays local. It is used in the study of finite flat commutative group schemes, namely in the two results on points of the Cartier dual being trivial under inertia conditions, [`HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual`](thm.html#HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual) and its $\mathbb{Z}_p$-variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom
    (R : Type*) [CommRing R] [IsLocalRing R]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Finite R A]
    (ε : A →ₐ[R] R)
    (O : Type*) [CommRing O] [Algebra R O] [IsLocalRing O] [IsLocalHom (algebraMap R O)] :
    IsLocalRing (O ⊗[R] A) := by sorry
