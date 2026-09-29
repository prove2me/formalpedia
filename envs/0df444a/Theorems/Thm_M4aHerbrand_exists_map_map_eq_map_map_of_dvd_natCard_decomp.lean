-- Prove2me | Theorems.Thm_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp
-- name    : M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/b5542bff-dd69-5fd1-abc9-207af19ab1ca
-- title:
--   Capturing an inflated idèle class over a second splitting field
-- statement:
--   Let $E$, $F$, $L$, $M$ be number fields with $E$-algebra structures on $F$, $L$, $M$ and $F$-, $L$-algebra structures on $M$ forming scalar towers over $E$, with $F/E$, $L/E$ and $M/E$ Galois, and let $p$ be a prime with $\mathrm{Gal}(M/E)$ a $p$-group. Data: descent structures $D_F$, $D_L$, $D_M$, each a monoid homomorphism from the relevant Galois group to ring automorphisms of the adèle ring of the field, compatible with the principal embedding and continuous; multiplicative Galois actions on the adèle unit groups agreeing with the induced actions on units; multiplicative Galois actions on $F^\times$ and $L^\times$ given by evaluation, together with morphisms $j_F$, $j_L$ of representations realising the principal-idèle maps; normal subgroups $S_F$, $S_L$ of $\mathrm{Gal}(M/E)$ with isomorphisms $\iota_F\colon \mathrm{Gal}(M/E)/S_F\cong\mathrm{Gal}(F/E)$, $\iota_L\colon\mathrm{Gal}(M/E)/S_L\cong\mathrm{Gal}(L/E)$ compatible with the embeddings into $M$; morphisms $J_F$, $J_L$ from the inflated idèle-unit representations of $F$, $L$ to that of $M$, given on points by the ring homomorphism $\beta$ of the base change `genuineBaseChange`; and, for each finite place $w$ of $F$, a morphism $\mathrm{pr}_w$ from the idèle units restricted to the decomposition subgroup of $w$ in $\mathrm{Gal}(F/E)$ to $(F_w)^\times$, given by the $w$-component map `finPart`. Assume every element of the stabiliser in $\mathrm{Gal}(F/E)$ of any infinite place of $F$ is trivial. Let $\alpha\in H^2(\mathrm{Gal}(F/E),F^\times)$ and assume that for each finite place $v$ of $E$, if the local component at the chosen place of $F$ above $v$ of $H^2(j_F)(\alpha)$ is nonzero, then $|\mathrm{Gal}(F/E)|$ divides the order of the decomposition subgroup in $\mathrm{Gal}(L/E)$ of every finite place $w'$ of $L$ lying under $v$. Then there exists $\alpha_L\in H^2(\mathrm{Gal}(L/E),L^\times)$ whose image under $H^2(j_L)$ followed by inflation along $\iota_L\circ(\,\cdot\,\bmod S_L)$ with coefficient map $J_L$ equals the image of $\alpha$ under $H^2(j_F)$ followed by inflation along $\iota_F\circ(\,\cdot\,\bmod S_F)$ with coefficient map $J_F$, in $H^2$ of $\mathrm{Gal}(M/E)$ acting on the idèle units of $M$.
--
--   This is Tate's "capture" step in the first proof of the reciprocity law: a class over $E$ split by $F$, inflated to the $p$-extension $M$ and viewed in idèles, is shown to come from a class split by the auxiliary field $L$, the local degree condition at the finite places where the class is locally nontrivial and the triviality of the infinite decomposition groups making the relevant local components vanish. It feeds into [`M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_map_map_eq_map_map_of_dvd_natCard_decomp.lean

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

theorem M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp
    (E F L M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra E F] [Algebra E L] [Algebra E M] [Algebra F M] [Algebra L M]
    [IsScalarTower E F M] [IsScalarTower E L M] [IsGalois E F] [IsGalois E L] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] (hM : IsPGroup p (M ≃ₐ[E] M))

    (DF : IdeleGaloisDescent (𝓞 F) E F) (DL : IdeleGaloisDescent (𝓞 L) E L) (DM : IdeleGaloisDescent (𝓞 M) E M)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactIF : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = DF.unitsAct g x)
    [MulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ]
    (hactIL : ∀ (g : (L ≃ₐ[E] L)) (x : (AdeleRing (𝓞 L) L)ˣ), g • x = DL.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (jF : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hjF : ∀ a : Fˣ, jF.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : (L ≃ₐ[E] L)) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    (jL : Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ ⟶ Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ)
    (hjL : ∀ a : Lˣ, jL.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a))

    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))
    (SL : Subgroup (M ≃ₐ[E] M)) [SL.Normal] (ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (L ≃ₐ[E] L))
    (hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y))

    (JF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJF : ∀ x : (AdeleRing (𝓞 F) F)ˣ, JF.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))
    (JL : Rep.res (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJL : ∀ x : (AdeleRing (𝓞 L) L)ˣ, JL.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange L M).β.toMonoidHom x))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2))

    (hdiv : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
          (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom α) ≠ 0 →
      ∀ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 E) = v →
        Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L w')) :
    ∃ αL : ↥(groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2),
      (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) JL 2).hom
          ((groupCohomology.map (MonoidHom.id (L ≃ₐ[E] L)) jL 2).hom αL) =
        (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) jF 2).hom α) := by sorry
