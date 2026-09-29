-- Prove2me | Theorems.Thm_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
-- name    : IsLocalRing.tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/6fdfebbb-f8b1-51d6-b70f-9afba16d1a0f
-- title:
--   Tensor product of module-finite local algebras over a local ring with algebraically closed residue field
-- statement:
--   Let $R$ be a commutative local ring whose residue field $\mathrm{ResidueField}(R)$ is algebraically closed, and let $A$ and $B$ be commutative $R$-algebras, each finite as an $R$-module and each a local ring; all three carrier types lie in a single universe. The conclusion is that the $R$-algebra tensor product $A \otimes_R B$, with its induced commutative ring structure, is again a local ring, i.e. it is nontrivial and has a unique maximal ideal. No separation, flatness or Noetherian hypothesis is imposed, and the residue fields of $A$ and $B$ are not assumed algebraically closed; the algebraic closedness is required only of the residue field of the base $R$.
--
--   This is the algebraic form of the statement that the fibre product of two connected finite schemes over a strictly henselian-type base (here: a local base with algebraically closed residue field) is connected, in the shape needed for local rings rather than for schemes. In this development it is used by [`HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one`](thm.html#HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one), where comultiplication lands in a tensor product whose locality controls the idempotents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem IsLocalRing.tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [IsLocalRing B] :
    IsLocalRing (A ⊗[R] B) := by sorry
