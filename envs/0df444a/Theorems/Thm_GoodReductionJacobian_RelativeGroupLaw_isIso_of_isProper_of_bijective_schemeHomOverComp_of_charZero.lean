-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
-- name    : GoodReductionJacobian.RelativeGroupLaw.isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6fbc381c-8e93-55a3-8cbd-ce1c235bdeab
-- title:
--   Proper bijective homomorphism over char-zero field is an isomorphism
-- statement:
--   Let $k$ be an algebraically closed field of characteristic zero. Let $g : G \to \operatorname{Spec} k$ be a scheme over $k$ carrying a relative group law `LG`, that is, for each $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set $\{\varphi : T \to G \mid \varphi \circ g = t\}$ of sections of $g$ over $t$, satisfying associativity, the two unit laws and left inversion, and natural with respect to morphisms $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$ (composition with $\psi$ commutes with multiplication); assume `LG` is commutative, i.e. its multiplication is commutative on the points over every such $t$. Let $h : H \to \operatorname{Spec} k$ be locally of finite type with $H$ reduced, and let `LH` be a relative group law on $h$. Let $p$ consist of a morphism $p.1 : G \to H$ with $p.1$ followed by $h$ equal to $g$, with $p.1$ proper, such that for every $t : T \to \operatorname{Spec} k$ and all sections $x, y$ of $g$ over $t$, composing the `LG`-product of $x$ and $y$ with $p$ gives the `LH`-product of the composites of $x$ and of $y$ with $p$. Assume further that composition with $p$ is a bijection from the sections of $g$ over $\mathrm{id}_{\operatorname{Spec} k}$ to those of $h$ over $\mathrm{id}_{\operatorname{Spec} k}$. Then $p.1$ is an isomorphism of schemes.
--
--   This is the standard characteristic-zero criterion: a proper homomorphism of group schemes over an algebraically closed field of characteristic zero which is bijective on rational points, with reduced locally of finite type target, is an isomorphism; the kernel is finite, hence the spectrum of a finite-dimensional commutative Hopf algebra, which is reduced by Cartier's theorem. It is used in the study of abelian schemes attached to Jacobians of curves with good reduction, where it supplies the morphism produced by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (LG : RelativeGroupLaw k g) (hcG : LG.IsCommutative)
    {H : Scheme.{u}} {h : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType h] [IsReduced H]
    (LH : RelativeGroupLaw k h)
    (p : SchemeHomOver g h) [IsProper p.1]
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) p =
        LH.mul t (NeronModelInfra.schemeHomOverComp x p) (NeronModelInfra.schemeHomOverComp y p))
    (hbij : Function.Bijective fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g =>
      NeronModelInfra.schemeHomOverComp x p) :
    IsIso p.1 := by sorry
