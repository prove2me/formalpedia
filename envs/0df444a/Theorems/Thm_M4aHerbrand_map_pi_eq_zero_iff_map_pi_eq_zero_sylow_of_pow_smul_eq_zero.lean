-- Prove2me | Theorems.Thm_M4aHerbrand_map_pi_eq_zero_iff_map_pi_eq_zero_sylow_of_pow_smul_eq_zero
-- name    : M4aHerbrand.map_pi_eq_zero_iff_map_pi_eq_zero_sylow_of_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/884501d4-fb4c-5263-803c-fd3d1612a17f
-- title:
--   Sylow descent for vanishing in degree-two idèle class cohomology
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $p$ be a prime and let $P$ be a Sylow $p$-subgroup of $G = \mathrm{Gal}(F/E)$, with fixed field $E' = F^{P}$. Over $E$ one is given: a descent datum $D$, that is a homomorphism from $G$ to the ring automorphisms of $\mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$ whose values are continuous and compatible with $\mathrm{alg}\colon F \to \mathbb{A}_F$ and the action on $F$; a multiplicative-distributive action of $G$ on $\mathbb{A}_F^{\times}$ agreeing with the induced action `D.unitsAct`; for each $w \in$ `HeightOneSpectrum` $(\mathcal{O}_F)$ a morphism $\mathrm{prG}\,w$ of representations from the restriction of $\mathbb{A}_F^{\times}$ to the decomposition subgroup of $w$ to the units of the completion at $w$, given on elements by the $w$-component `finPart` $w$; an action of $G$ on the idèle class group $\mathbb{A}_F^{\times}/\mathrm{alg}(F^{\times})$ agreeing with `D.classAct`; and a morphism $\pi$ of $G$-representations given on elements by the quotient map $\mathbb{A}_F^{\times} \to C_F$. The same package $(D', \mathrm{prG}', \pi')$ is given over $E'$ for $\mathrm{Gal}(F/E')$. Further, $\Theta\colon P \xrightarrow{\sim} \mathrm{Gal}(F/E')$ is a multiplicative isomorphism acting on $F$ as the inclusion does, and $\psi$ is the morphism of $P$-representations, the identity on elements, between the two restrictions of $\mathbb{A}_F^{\times}$ along $\Theta$ and along $P \hookrightarrow G$. Finally, $x \in H^{2}(G, \mathbb{A}_F^{\times})$ and $x' \in H^{2}(\mathrm{Gal}(F/E'), \mathbb{A}_F^{\times})$ satisfy $(\Theta,\psi)_{*} x' = \mathrm{res}_{P} x$, and $p^{k} \cdot x = 0$ for some $k \in \mathbb{N}$. Then $H^{2}(\pi)(x) = 0$ if and only if $H^{2}(\pi')(x') = 0$.
--
--   This is the Sylow-descent bookkeeping step which transfers the vanishing of the image of a $p$-power-torsion degree-two idèle cohomology class in the idèle class group between a full Galois layer $F/E$ and the layer $F/F^{P}$ over the fixed field of a Sylow $p$-subgroup, using that the index of $P$ is coprime to $p$. It is used in the passage from $p$-group layers to arbitrary finite Galois layers in the construction of the global fundamental class, and is cited by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_pi_eq_zero_iff_map_pi_eq_zero_sylow_of_pow_smul_eq_zero.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.map_pi_eq_zero_iff_map_pi_eq_zero_sylow_of_pow_smul_eq_zero
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : (IdeleClassGroup (𝓞 F) F)), g • c = D.classAct g c)
    (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
    (hπ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, (π).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 F) F)))
    (D' : IdeleGaloisDescent (𝓞 F) ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F)
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w)) (w.adicCompletion F)ˣ)
    (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (c : (IdeleClassGroup (𝓞 F) F)), g • c = D'.classAct g c)
    (π' : Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (IdeleClassGroup (𝓞 F) F))
    (hπ' : ∀ x : (AdeleRing (𝓞 F) F)ˣ, (π').hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 F) F)))
    (Θ : ↥(P : Subgroup (F ≃ₐ[E] F)) ≃* (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F))
    (hΘ : ∀ (s : ↥(P : Subgroup (F ≃ₐ[E] F))) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
    (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hψ : ∀ y, ψ.hom y = y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
      (groupCohomology.map (P : Subgroup (F ≃ₐ[E] F)).subtype (𝟙 (Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x)
    (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0) :
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = 0 ↔
      (groupCohomology.map (MonoidHom.id (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) π' 2).hom x' = 0 := by sorry
