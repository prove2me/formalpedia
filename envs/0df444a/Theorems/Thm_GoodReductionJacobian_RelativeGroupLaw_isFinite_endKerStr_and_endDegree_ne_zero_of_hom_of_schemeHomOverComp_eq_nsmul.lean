-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/3d4f76d5-a565-5bb6-aff3-f103145a4173
-- title:
--   Finite kernel and non-zero degree for a factor of [M]
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a morphism. Let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over each $t : T \to \operatorname{Spec} K$, with multiplication, unit and inverse satisfying the group axioms and compatible with base change along $\psi : T' \to T$; assume $L$ is commutative, i.e. its multiplication on each such set is commutative. Assume $f$ carries the property bundle consisting of smoothness, properness, connectedness of the fibres of $f$ on underlying spaces and existence of a relative group law, and that $f$ is smooth of relative dimension $g$. Let $\beta, \gamma$ be endomorphisms of $A$ over $f$, i.e. morphisms $A \to A$ whose composite with $f$ is $f$, and suppose each of them is a homomorphism for $L$ in the sense that right composition with it takes the product of two sections over any base to the product of the composites. Let $M \neq 0$ be a natural number, and suppose that $\beta$ followed by $\gamma$ equals the $M$-fold $L$-multiple of the identity section $\mathrm{id}_A$. Then the second projection of the pullback of $\beta$ along the unit section $L.\mathrm{one}(\mathbf{1}_{\operatorname{Spec} K})$ — the structural morphism of the kernel of $\beta$ — is a finite morphism, and $L.\mathrm{endDegree}\,\beta$, defined as the finrank of that kernel at the closed point of $\operatorname{Spec} K$ when it is finite and $0$ otherwise, is non-zero.
--
--   This is the standard step showing that an endomorphism of an abelian variety admitting a right factorisation of a non-zero multiplication map $[M]$ has finite kernel and hence non-zero degree. It is used in the quaternionic setting, where an endomorphism coming from an order with non-zero reduced norm is shown to have finite kernel of rank the square of that norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_endDegree_ne_zero_of_hom_of_schemeHomOverComp_eq_nsmul
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (β γ : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
        L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (M : ℕ) (hM : M ≠ 0)
    (hβγ : NeronModelInfra.schemeHomOverComp β γ = L.nsmul f M RelativeGroupLaw.idPoint) :
    IsFinite (L.endKerStr β) ∧ L.endDegree β ≠ 0 := by sorry
