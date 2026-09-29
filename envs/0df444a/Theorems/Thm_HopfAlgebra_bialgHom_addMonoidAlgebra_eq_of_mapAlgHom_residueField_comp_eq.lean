-- Prove2me | Theorems.Thm_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
-- name    : HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b2f9c147-c3ab-5cc7-bb8b-3f2a655fe7e4
-- title:
--   Bialgebra maps to a group algebra are determined modulo 𝔪
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m$ and residue field $\kappa =$ `ResidueField R`, and let $H$ be a commutative ring (in the same universe as $R$) carrying a Hopf algebra structure over $R$, finite and flat as an $R$-module, and cocommutative as an $R$-coalgebra. Let $M$ be a finite additive commutative group, and let $R[M] =$ `AddMonoidAlgebra R M` be the associated group algebra. Let $\psi, \psi' \colon H \to R[M]$ be two homomorphisms of $R$-bialgebras, i.e. $R$-algebra maps that are simultaneously maps of $R$-coalgebras. Suppose that the underlying $R$-algebra maps become equal after change of coefficients along the canonical map $R \to \kappa$: the composite of $\psi$ with the coefficientwise map $R[M] \to \kappa[M]$ induced by `Algebra.ofId R (ResidueField R)` equals the composite of $\psi'$ with that same map, as $R$-algebra homomorphisms $H \to \kappa[M]$. The conclusion is that $\psi = \psi'$ as bialgebra homomorphisms.
--
--   This is the uniqueness half of the lifting statement for homomorphisms from a split group of multiplicative type $D(M) = \operatorname{Spec} R[M]$ into a finite flat commutative group scheme $\operatorname{Spec} H$: the restriction map on homomorphism sets to the special fibre is injective, and for this only locality of $R$ is needed. It is used in the existence-and-uniqueness statement [`HopfAlgebra.existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#HopfAlgebra.existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing), where the base is assumed henselian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ ψ' : H →ₐc[R] AddMonoidAlgebra R M)
    (h : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ' : H →ₐ[R] AddMonoidAlgebra R M)) :
    ψ = ψ' := by sorry
