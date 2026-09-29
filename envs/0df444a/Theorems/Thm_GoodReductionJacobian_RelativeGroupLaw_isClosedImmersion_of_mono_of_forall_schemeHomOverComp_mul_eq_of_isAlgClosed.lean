-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/b7fb34e8-8bef-5ea8-970b-ad23e3c99784
-- title:
--   Monomorphic homomorphism with reduced source is a closed immersion
-- statement:
--   Let $k$ be an algebraically closed field, let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes that is locally of finite type and quasi-compact with $G$ reduced, and let $g \colon H \to \operatorname{Spec} k$ be locally of finite type and quasi-compact. Suppose given relative group laws $L$ on $f$ and $M$ on $g$: for each scheme $T$ with a structure morphism $t \colon T \to \operatorname{Spec} k$, group operations (multiplication, unit, inverse, satisfying associativity, the unit laws and left inverses) on the set of $k$-morphisms over $\operatorname{Spec} k$ from $t$ to the respective structure morphism, i.e. on $\{\,x \colon T \to G \mid x \text{ followed by } f = t\,\}$ resp. with $H$, $g$, these operations being compatible with precomposition by any $\psi \colon T' \to T$ over $\operatorname{Spec} k$. Let $\varphi \colon G \to H$ satisfy $\varphi$ followed by $g$ equals $f$, assume $\varphi$ is a monomorphism of schemes, and assume that for every $t \colon T \to \operatorname{Spec} k$ and all $T$-points $x, y$ of $G$ over $k$ one has $L.\mathrm{mul}\,t\,x\,y$ followed by $\varphi$ equal to $M.\mathrm{mul}\,t$ applied to $x$ followed by $\varphi$ and $y$ followed by $\varphi$. Then $\varphi$ is a closed immersion. Only multiplicativity of $\varphi$ is assumed, not compatibility with units or inverses.
--
--   This is the statement that a monomorphism of group schemes of finite type over a field is a closed immersion, here over an algebraically closed field and with the source assumed reduced, with group structures presented functorially on points. It is used in the analysis of affineness of smooth group schemes arising in the construction of Néron models for Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced G] (L : RelativeGroupLaw k f)
    {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]
    (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g) [Mono φ.1]
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosedImmersion φ.1 := by sorry
