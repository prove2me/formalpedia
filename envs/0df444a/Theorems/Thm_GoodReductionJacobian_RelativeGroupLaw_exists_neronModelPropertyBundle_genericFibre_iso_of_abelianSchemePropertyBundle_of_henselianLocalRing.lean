-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5c11edd6-e71a-56eb-a4e7-e360db4adcd5
-- title:
--   Néron models over a henselian discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain and a henselian local ring, and let $K$ be a field which is an $R$-algebra and a fraction field of $R$. Let $AK$ be a scheme with a morphism $gK : AK \to \operatorname{Spec} K$, let $LAK$ be a relative group law for $gK$ over $K$ (a group structure on the $K$-morphisms $T \to AK$ over each $t : T \to \operatorname{Spec} K$, with multiplication, unit and inverse satisfying the group axioms and compatible with precomposition in $T$), and assume `AbelianSchemePropertyBundle K gK`: $gK$ is smooth and proper, each fibre of $gK$ over a point of $\operatorname{Spec} K$ is connected, and $gK$ carries some relative group law. Then there exist a scheme $B$, a morphism $g : B \to \operatorname{Spec} R$, a relative group law $LB$ for $g$ over $R$, and a morphism $e$ from the pullback $B \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (via `pullback.snd` against $\operatorname{Spec}$ of $R \to K$) to $AK$ commuting with the structure morphisms to $\operatorname{Spec} K$, such that: `NeronModelPropertyBundle R K g` holds, i.e. $g$ is smooth, separated, locally of finite type and quasi-compact and for every smooth $t : T \to \operatorname{Spec} R$ the generic-fibre restriction map on sections is bijective; $LB$ is commutative; the underlying morphism of $e$ is an isomorphism; and $e$ is a homomorphism, in that for every $t : T \to \operatorname{Spec} K$ and sections $x,y$ of the generic fibre, the composite of $(LB.\mathrm{genericFibre}\ K).\mathrm{mul}\ t\ x\ y$ with $e$ equals $LAK.\mathrm{mul}$ of the composites of $x$ and $y$ with $e$.
--
--   This is Néron's existence theorem for Néron models of abelian varieties, in the case of a henselian discrete valuation base ring: the abelian variety over $K$ acquires a smooth separated finite-type $R$-model with the Néron mapping property, carrying a commutative relative group law whose generic fibre is identified with the given one. It is used in the construction of good-reduction models in the Čerednik–Drinfeld setting and in the treatment of Jacobians with relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (LAK : RelativeGroupLaw K gK)
    (hAK : AbelianSchemePropertyBundle K gK) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      NeronModelPropertyBundle R K g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LB.mul t x y = LB.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) := by sorry
