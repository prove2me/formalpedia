-- Prove2me | Theorems.Thm_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
-- name    : M4aHerbrand.map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c0eb4be3-cec2-5110-bf3c-4597afa9376f
-- title:
--   Inflation commutes with taking the W-component of idèles
-- statement:
--   Let $E \subseteq F \subseteq M$ be number fields, with $M$ an $F$-algebra and $F$ an $E$-algebra forming a scalar tower over $E$, and assume the unit groups $(\mathbb{A}_F)^\times$ and $(\mathbb{A}_M)^\times$ of the adele rings carry multiplicative-distributive actions of $F \simeq_{\mathrm{alg}[E]} F$ and $M \simeq_{\mathrm{alg}[E]} M$ respectively, so that each becomes a $\mathbb{Z}$-representation via `Rep.ofMulDistribMulAction`. Given a normal subgroup $S$ of $M \simeq_{\mathrm{alg}[E]} M$ and an isomorphism $\iota \colon (M \simeq_{\mathrm{alg}[E]} M)/S \cong (F \simeq_{\mathrm{alg}[E]} F)$ with $\iota(\bar g)$ agreeing with $g$ on $F$ under $F \to M$ (hypothesis `hι`); a morphism $J$ from the restriction of $(\mathbb{A}_F)^\times$ along $\iota \circ \mathrm{mk}'$ to $(\mathbb{A}_M)^\times$ whose underlying map is induced by the ring homomorphism $\beta$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange F M`](def/M4aHerbrand_GenuineDescent.html#L87) (hypothesis `hJ`); a height-one prime $W$ of $\mathcal{O}_M$ with $w_1 = W \cap \mathcal{O}_F$; morphisms $\mathrm{prG}$, $\mathrm{prM}$ from the restrictions of the idèle representations to the decomposition subgroups $\mathrm{decomp}\,E\,F\,w_1$ and $\mathrm{decomp}\,E\,M\,W$ (the decomposition subgroups of the valuation subrings of the $w_1$- and $W$-adic valuations) into $(F_{w_1})^\times$, $(M_W)^\times$, whose underlying maps are the coordinate homomorphisms `finPart` at $w_1$ and at $W$; a monoid homomorphism $r$ from $\mathrm{decomp}\,E\,M\,W$ to $\mathrm{decomp}\,E\,F\,w_1$ with $r(\sigma)$ agreeing with $\sigma$ on $F$; and a morphism $\mathrm{iD}$ from the restriction along $r$ of $(F_{w_1})^\times$ to $(M_W)^\times$ induced by the semialgebra homomorphism $F_{w_1} \to M_W$ attached to the extension $\langle W, \mathrm{rfl}\rangle$ of $w_1$. Then for every $n \in \mathbb{N}$ and every $y \in H^n((F \simeq_{\mathrm{alg}[E]} F), (\mathbb{A}_F)^\times)$, the image of $y$ under inflation along $(\iota, J)$ followed by the map induced by $(\mathrm{decomp}\,E\,M\,W \hookrightarrow M \simeq_{\mathrm{alg}[E]} M, \mathrm{prM})$ coincides with its image under the map induced by $(\mathrm{decomp}\,E\,F\,w_1 \hookrightarrow F \simeq_{\mathrm{alg}[E]} F, \mathrm{prG})$ followed by the map induced by $(r, \mathrm{iD})$, as elements of $H^n(\mathrm{decomp}\,E\,M\,W, (M_W)^\times)$.
--
--   This is the cohomology-class form of the compatibility of local coordinates with inflation: the $W$-component of an inflated idèle class is the local inflation, along the surjection of decomposition groups and the inclusion $F_{w_1}^\times \subseteq M_W^\times$, of its $w_1$-component. It feeds the comparison of local invariants at $W$ and at $w_1$ used in the Herbrand-quotient part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (W : HeightOneSpectrum (𝓞 M))
    (prG : Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (hprG : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prG.hom (Additive.ofMul x) = Additive.ofMul (finPart (W.under (𝓞 F)) x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))

    (r : ↥(NumberField.PlaceDecomp.decomp E M W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x))
    (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM n).hom
        ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J n).hom y) =
      (groupCohomology.map r iD n).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype prG n).hom y) := by sorry
