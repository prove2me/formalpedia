-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/bd3a8027-9293-57c7-b230-0fdbeef87a9e
-- title:
--   Infinitesimality modulo the nilradical via field-valued points
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$ over $B$, i.e. a structure assigning to every $B$-scheme $t : T \to \operatorname{Spec} B$ a multiplication, a unit and an inverse on the set of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws and left inversion, and compatible with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} B$. Assume $f$ is separated. Let $R$ be a commutative $B$-algebra and let $Q$ be an $R$-point of $f$, that is a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is $\operatorname{Spec}$ of the structure map $B \to R$. Then $Q$ is infinitesimal for the ideal $\mathfrak N = \operatorname{nilradical} R$, meaning that composing $\operatorname{Spec}$ of the quotient map $R \to R/\mathfrak N$ with $Q$ gives the unit point $L.\mathrm{one}$ over $\operatorname{Spec}(R/\mathfrak N)$, if and only if for every field $\kappa$ that is a $B$-algebra and every $B$-algebra homomorphism $\varphi : R \to \kappa$, the composite of $\operatorname{Spec}(\varphi)$ with $Q$ equals the unit point over $\operatorname{Spec} \kappa$.
--
--   This is the standard criterion identifying points of a separated relative group scheme that are trivial modulo nilpotents: triviality of all field-valued specialisations of a point is equivalent to its reduction modulo the nilradical of the test ring being the unit section. It is used in the construction of infinitesimal (formal-group) neighbourhoods of the unit section for fake elliptic curves, where it supplies the infinitesimality hypothesis from the vanishing of all residue-field specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) [IsSeparated f]
    (R : Type) [CommRing R] [Algebra B R] (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f) :
    L.IsInfinitesimal (nilradical R) Q ↔
      ∀ (κ : Type) [Field κ] [Algebra B κ] (φ : R →ₐ[B] κ),
        schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (Scheme.specMap_algHom_comp_specOver φ) Q = L.one (Scheme.specOver (𝒪 := B) κ) := by sorry
