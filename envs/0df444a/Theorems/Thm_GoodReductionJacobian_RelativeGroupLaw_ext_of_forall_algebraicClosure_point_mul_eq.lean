-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.ext_of_forall_algebraicClosure_point_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/f7370c2c-08b7-55e6-a4ec-29f9210dcd5f
-- title:
--   Rigidity: a relative group law is determined on ̄ K-points
-- statement:
--   Let $R$ be a commutative integral domain, let $K$ be a field that is a fraction field of $R$, and let $\overline K$ be a field that is an algebraic closure of $K$, equipped with an $R$-algebra structure compatible with those of $K$ over $R$ and of $\overline K$ over $K$. Let $G$ be a scheme and $f \colon G \to \operatorname{Spec} R$ a morphism that is smooth and separated. For a morphism $t \colon T \to \operatorname{Spec} R$ write $G(t)$ for the set of pairs consisting of a morphism $\varphi \colon T \to G$ together with the identity $\varphi$ followed by $f$ equals $t$. Let $L_1, L_2$ be two relative group laws on $f$ over $R$: each provides, for every such $t$, a multiplication $G(t) \times G(t) \to G(t)$, a unit and an inversion, satisfying associativity, both unit laws and the left inverse law, and such that the multiplication is natural in the base, i.e. compatible with composition along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume that for all $x, y$ in $G(\operatorname{Spec}\overline K \to \operatorname{Spec} R)$, the morphism induced by $\operatorname{Spec}$ of the structure map $R \to \overline K$, the two multiplications agree: $L_1.\mathrm{mul}\,x\,y = L_2.\mathrm{mul}\,x\,y$. Then $L_1 = L_2$, so in particular their units and inversions also coincide.
--
--   This is the rigidity statement that a group law on a smooth separated $R$-scheme is determined by the group structure it induces on geometric generic points; it is the uniqueness half of the construction of group structures on Néron models by extension from the generic fibre. It is used in the construction of points on the Néron model attached to a modular Jacobian, in the verification that a base-changed relative group law is the expected one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.ext_of_forall_algebraicClosure_point_mul_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar]
    [IsScalarTower R K Kbar]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    [Smooth f] [IsSeparated f]
    (L₁ L₂ : RelativeGroupLaw R f)
    (hmul : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) f,
      L₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y =
        L₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y) :
    L₁ = L₂ := by sorry
