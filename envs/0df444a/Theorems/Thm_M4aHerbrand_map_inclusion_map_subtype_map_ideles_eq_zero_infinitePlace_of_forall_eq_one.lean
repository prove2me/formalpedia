-- Prove2me | Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one
-- name    : M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3596d6f2-8888-5caf-9e93-f312e0fb26e4
-- title:
--   Vanishing of archimedean coordinates of inflated idele classes in H²
-- statement:
--   Let $E \subseteq F \subseteq M$ be number fields (a scalar tower of algebras $E \to F \to M$) with $F/E$ and $M/E$ Galois. Let $DF$, $DM$ be Galois descent data for the idele rings, i.e. continuous actions of $\operatorname{Gal}(F/E)$ on $\mathbb{A}_F$ and of $\operatorname{Gal}(M/E)$ on $\mathbb{A}_M$ by ring automorphisms extending the action on the base field; it is assumed that the given multiplicative distributive actions on $\mathbb{A}_F^\times$ and $\mathbb{A}_M^\times$ are the induced unit actions. Let $SF \trianglelefteq \operatorname{Gal}(M/E)$ together with an isomorphism $\iota_F : \operatorname{Gal}(M/E)/SF \simeq \operatorname{Gal}(F/E)$ compatible with restriction of automorphisms along $F \to M$, and let $JF$ be a morphism from the $\operatorname{Gal}(M/E)$-representation obtained by restricting $\mathbb{A}_F^\times$ along $\iota_F \circ \mathrm{mk}$ to $\mathbb{A}_M^\times$, given on points by the canonical ring homomorphism $\mathbb{A}_F \to \mathbb{A}_M$ of `genuineBaseChange` on units. Let $S \le \operatorname{Gal}(M/E)$ be any subgroup, and for each infinite place $V$ of $M$ let $\mathrm{prInfH}\,V$ be the morphism of $S \cap D_V$-representations from $\mathbb{A}_M^\times$ to $(M_V)^\times$ given by taking the infinite part and evaluating at $V$, where $D_V$ is the stabiliser of $V$ in $\operatorname{Gal}(M/E)$. Assume every infinite place $v$ of $F$ has trivial stabiliser in $\operatorname{Gal}(F/E)$. Then for every $y \in H^2(\operatorname{Gal}(F/E), \mathbb{A}_F^\times)$ and every infinite place $V$ of $M$, the image of $y$ under inflation along $\iota_F \circ \mathrm{mk}$ with $JF$, followed by restriction to $S$, followed by restriction to $S \cap D_V$ together with $\mathrm{prInfH}\,V$, is $0$ in $H^2(S \cap D_V, (M_V)^\times)$.
--
--   This is the archimedean half of the local-coordinate vanishing used to control the image of inflated idele classes: the coordinate at $V$ of an inflated class is the inflation of the coordinate of $y$ at the infinite place of $F$ below $V$, which lies in $H^2$ of the trivial group when no infinite place of $F$ is ramified over $E$. It feeds the cyclic-capture argument [`M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_infinitePlace_of_forall_eq_one
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]

    (DF : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactIF : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = DF.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (JF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJF : ∀ x : (AdeleRing (𝓞 F) F)ˣ, JF.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (S : Subgroup (M ≃ₐ[E] M))
    (prInfH : ∀ V : InfinitePlace M,
      Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.InfPlaceDecomp.decomp E M V ≤ S))
          (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.InfPlaceDecomp.decomp E M V ≤ NumberField.InfPlaceDecomp.decomp E M V))
          (NumberField.InfPlaceDecomp.localUnits E M V))
    (hprInfH : ∀ (V : InfinitePlace M) (x : (AdeleRing (𝓞 M) M)ˣ),
      (prInfH V).hom (Additive.ofMul x) = Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace M => u.Completion) V) (infPart x)))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)) :
    ∀ V : InfinitePlace M,
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.InfPlaceDecomp.decomp E M V ≤ S)) (prInfH V) 2).hom
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom
          ((groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom y)) = 0 := by sorry
