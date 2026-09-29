-- Prove2me | Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
-- name    : M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/20f1d2b8-4d2c-5129-8e54-1ddd697f3e0e
-- title:
--   Local coordinates and idèle cohomology at a subgroup H
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$: a homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ that extends the Galois action on $F$ and is continuous. Fix a multiplicative distributive action of the Galois group on $\mathbb{A}_F^{\times}$ agreeing, by `hactI`, with the one induced by $D$ on units, and let $H$ be a subgroup of the Galois group. Let $\mathbb{I}$ denote the $\mathbb{Z}$-representation $\mathbb{A}_F^{\times}$ (written additively) restricted to $H$. Assume given, for each finite place $w$ of $F$, a morphism `prH w` of representations of $H \cap D_w$ from $\mathbb{I}$ restricted to $H \cap D_w$ to the units $(F_w)^{\times}$ with their $D_w$-action restricted to $H \cap D_w$, pinned by `hprH` to be $x \mapsto$ the $w$-component `finPart w x` of an idèlic unit; and, for each infinite place $v$ of $F$, a morphism `prInfH v` into [`NumberField.InfPlaceDecomp.localUnits E F v`](def/NumberField_ArchimedeanIdeleModule.html#L142), pinned by `hprInfH` to be evaluation at $v$ of the archimedean part `infPart x`. Fix $n \in \mathbb{N}$. Writing the $w$- (resp. $v$-) coordinate of a class in $H^{n+1}(H, \mathbb{I})$ for its image under the map in degree $n+1$ induced by the inclusion $H \cap D_w \leq H$ together with `prH w` (resp. `prInfH v`), the conclusion is the conjunction of three assertions: (i) a class all of whose finite and infinite coordinates vanish is zero; (ii) for each class the set of finite places $w$ of $F$ with nonvanishing coordinate is finite; (iii) for every finite set $T$ of finite places of the fixed field $F^H =$ `IntermediateField.fixedField H`, every family $y$ assigning to each finite place $v$ of $F^H$ a class in $H^{n+1}(H \cap D_{w(v)}, (F_{w(v)})^{\times})$ for the chosen place $w(v) =$ [`NumberField.PlaceAbove.above`](def/NumberField_PlaceAbove.html#L27) of $F$ above $v$, and every family $y_{\infty}$ assigning to each infinite place $v$ of $F^H$ a class in $H^{n+1}$ of the local units at the chosen infinite place [`NumberField.ArchIdele.above`](def/NumberField_ArchimedeanIdeleModule.html#L155) of $F$ above $v$, there is a class $x \in H^{n+1}(H, \mathbb{I})$ whose coordinate at $w(v)$ equals $y\,v$ for $v \in T$, vanishes for $v \notin T$, and whose coordinate at the chosen infinite place above $v$ equals $y_{\infty} v$ for every infinite place $v$ of $F^H$.
--
--   This is the Shapiro-type description of the cohomology of the idèle group at a subgroup $H$ of the Galois group: the local coordinates "restrict to $H \cap D_w$, then project to the $w$-component" identify $H^{n+1}(H, \mathbb{A}_F^{\times})$ with the direct sum of the local cohomology groups indexed by the places of the fixed field $F^H$, stated as injectivity, finiteness of support and surjectivity with prescribed coordinate values. It is used in the comparison of corestriction and of Herbrand-type sums over decomposition groups, namely by [`M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp) and [`M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp Pointwise

theorem M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F))

    (prH : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H))
          (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ NumberField.PlaceDecomp.decomp E F w))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hprH : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ),
      (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (prInfH : ∀ v : InfinitePlace F,
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.InfPlaceDecomp.decomp E F v ≤ H))
          (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.InfPlaceDecomp.decomp E F v ≤ NumberField.InfPlaceDecomp.decomp E F v))
          (NumberField.InfPlaceDecomp.localUnits E F v))
    (hprInfH : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ),
      (prInfH v).hom (Additive.ofMul x) = Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (n : ℕ) :

    (∀ x : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) (n + 1),
      (∀ w : HeightOneSpectrum (𝓞 F),
        (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H)) (prH w) (n + 1)).hom x = 0) →
      (∀ v : InfinitePlace F,
        (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.InfPlaceDecomp.decomp E F v ≤ H)) (prInfH v) (n + 1)).hom x = 0) →
      x = 0) ∧

    (∀ x : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) (n + 1),
      {w : HeightOneSpectrum (𝓞 F) |
        (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H)) (prH w) (n + 1)).hom x ≠ 0}.Finite) ∧

    (∀ (T : Finset (HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))))
      (y : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        groupCohomology (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v) ≤ NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)) (n + 1))
      (yinf : ∀ v : InfinitePlace ↥(IntermediateField.fixedField H),
        groupCohomology (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above ↥(IntermediateField.fixedField H) F v) ≤ NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above ↥(IntermediateField.fixedField H) F v)))
          (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above ↥(IntermediateField.fixedField H) F v))) (n + 1)),
      ∃ x : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) (n + 1),
        (∀ v ∈ T,
          (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) (n + 1)).hom x = y v) ∧
        (∀ v ∉ T,
          (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) (n + 1)).hom x = 0) ∧
        (∀ v : InfinitePlace ↥(IntermediateField.fixedField H),
          (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above ↥(IntermediateField.fixedField H) F v) ≤ H)) (prInfH (NumberField.ArchIdele.above ↥(IntermediateField.fixedField H) F v)) (n + 1)).hom x = yinf v)) := by sorry
