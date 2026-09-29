-- Prove2me | Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
-- name    : M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f17193f4-c68a-571e-90c9-773cfe91e028
-- title:
--   Vanishing of local components of an inflated idèle class
-- statement:
--   Fix number fields $E, F, L, M$ with $E$-algebra structures on $F, L, M$ and $F$-, $L$-algebra structures on $M$ forming towers $E\subseteq F\subseteq M$ and $E\subseteq L\subseteq M$, with $F/E$, $L/E$ and $M/E$ Galois, and a prime $p$ such that $\mathrm{Gal}(M/E)$ is a $p$-group. Assume given idèle Galois descent data $D_F$, $D_M$ (monoid homomorphisms from the Galois group of $F/E$, resp. $M/E$, to the ring automorphisms of the adèle ring, compatible with the structure map of the field and continuous), together with multiplicative-distributive actions of $\mathrm{Gal}(F/E)$ on $(\mathbb{A}_F)^\times$ and of $\mathrm{Gal}(M/E)$ on $(\mathbb{A}_M)^\times$ that agree with the actions on units induced by $D_F$ and $D_M$; normal subgroups $S_F, S_L\le\mathrm{Gal}(M/E)$ with isomorphisms $\iota_F:\mathrm{Gal}(M/E)/S_F\cong\mathrm{Gal}(F/E)$ and $\iota_L:\mathrm{Gal}(M/E)/S_L\cong\mathrm{Gal}(L/E)$ compatible with the embeddings $F\to M$ and $L\to M$; a morphism $J_F$ of representations from the restriction of $(\mathbb{A}_F)^\times$ along $\mathrm{Gal}(M/E)\to\mathrm{Gal}(M/E)/S_F\xrightarrow{\iota_F}\mathrm{Gal}(F/E)$ to $(\mathbb{A}_M)^\times$, acting on points as the map on units induced by the base-change ring homomorphism $\beta$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange F M`](def/M4aHerbrand_GenuineDescent.html#L87); for each height-one prime $w$ of $\mathcal{O}_F$ a morphism $\mathrm{prG}\,w$ from the restriction of $(\mathbb{A}_F)^\times$ to the decomposition subgroup $\mathrm{decomp}\,E\,F\,w$ (the decomposition subgroup of the valuation subring of $w$) to $(F_w)^\times$, acting as the local component map `finPart w`; and for each height-one prime $W$ of $\mathcal{O}_M$ a morphism $\mathrm{prH}\,W$ of representations of $S_L\cap\mathrm{decomp}\,E\,M\,W$, from $(\mathbb{A}_M)^\times$ restricted through $S_L$ to $(M_W)^\times$ restricted from $\mathrm{decomp}\,E\,M\,W$, again acting as `finPart W`. Let $y$ be a class in $H^2$ of the representation of $\mathrm{Gal}(F/E)$ on $(\mathbb{A}_F)^\times$, and assume that for every height-one prime $v$ of $\mathcal{O}_E$, if the image of $y$ under the degree-$2$ map induced by the inclusion $\mathrm{decomp}\,E\,F\,(\mathrm{above}\,E\,F\,v)\hookrightarrow\mathrm{Gal}(F/E)$ and $\mathrm{prG}$ at the chosen prime $\mathrm{above}\,E\,F\,v$ is nonzero, then for every height-one prime $w'$ of $\mathcal{O}_L$ lying over $v$ one has $\#\mathrm{Gal}(F/E)\mid\#\,\mathrm{decomp}\,E\,L\,w'$. The conclusion is that for every height-one prime $W$ of $\mathcal{O}_M$, the class obtained from $y$ by the degree-$2$ map along $(\iota_F\circ\text{quotient},J_F)$, then the map along $S_L\hookrightarrow\mathrm{Gal}(M/E)$ with the identity, then the map along $S_L\cap\mathrm{decomp}\,E\,M\,W\hookrightarrow S_L$ with $\mathrm{prH}\,W$, is zero.
--
--   This is the per-place vanishing statement behind the Hasse-principle step of Tate's capture argument: after inflating an idèle cohomology class from $\mathrm{Gal}(F/E)$ to $\mathrm{Gal}(M/E)$ and restricting to $S_L=\mathrm{Gal}(M/L)$, its local component at each finite place $W$ of $M$ dies, the local degree hypothesis at places where the component of $y$ is nonzero forcing the relevant multiple of the local fundamental class to vanish. It is used by [`M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp.lean

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
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
    (E F L M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra E F] [Algebra E L] [Algebra E M] [Algebra F M] [Algebra L M]
    [IsScalarTower E F M] [IsScalarTower E L M] [IsGalois E F] [IsGalois E L] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] (hM : IsPGroup p (M ≃ₐ[E] M))

    (DF : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactIF : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = DF.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))
    (SL : Subgroup (M ≃ₐ[E] M)) [SL.Normal] (ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (L ≃ₐ[E] L))
    (hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y))

    (JF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJF : ∀ x : (AdeleRing (𝓞 F) F)ˣ, JF.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (prH : ∀ W : HeightOneSpectrum (𝓞 M),
      Rep.res (Subgroup.inclusion (inf_le_left : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ SL))
          (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))
    (hprH : ∀ (W : HeightOneSpectrum (𝓞 M)) (x : (AdeleRing (𝓞 M) M)ˣ), (prH W).hom (Additive.ofMul x) = Additive.ofMul (finPart W x))

    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

    (hdiv : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
          (prG (NumberField.PlaceAbove.above E F v)) 2).hom y ≠ 0 →
      ∀ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 E) = v →
        Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L w')) :
    ∀ W : HeightOneSpectrum (𝓞 M),
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ SL)) (prH W) 2).hom
        ((groupCohomology.map SL.subtype (𝟙 (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom
          ((groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom y)) = 0 := by sorry
