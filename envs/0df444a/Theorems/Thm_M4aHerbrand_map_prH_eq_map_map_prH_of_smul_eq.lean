-- Prove2me | Theorems.Thm_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq
-- name    : M4aHerbrand.map_prH_eq_map_map_prH_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e3e6f1c4-c682-5edb-95b4-00907bcd7cd4
-- title:
--   Local coordinate maps at w and hw agree up to conjugation
-- statement:
--   Let $F/E$ be a Galois extension of number fields with group $G = \mathrm{Gal}(F/E)$, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism $G \to \mathrm{RingAut}(\mathbb{A}_F)$ whose values are continuous and compatible with the structure map $F \to \mathbb{A}_F$. Assume a multiplicative distributive action of $G$ on $\mathbb{A}_F^\times$ which, by hypothesis, is the one induced by $D$ through `Units.mapEquiv`. Fix a subgroup $H \le G$, and write $D_w \le G$ for the decomposition subgroup of the valuation subring of $w$ at a finite place $w$ of $F$. Given, for each $w$, a morphism $\mathrm{pr}^H_w$ of $(H \cap D_w)$-representations from the restriction of the additive representation $\mathbb{A}_F^\times$ to $H \cap D_w$ to the restriction of $F_w^\times$ along $H \cap D_w \le D_w$, whose underlying map is the $w$-component $x \mapsto$ `finPart w x`; a place $w$, an element $h \in H$ with $h \cdot w = w_1$, a monoid homomorphism $c_h \colon H \cap D_{w_1} \to H \cap D_w$ with $c_h(x) = h^{-1} x h$, and a morphism $T_h$ of $(H \cap D_{w_1})$-representations from $\mathrm{Res}_{c_h} F_w^\times$ to $F_{w_1}^\times$ whose underlying map is the transport isomorphism $F_w \cong F_{w_1}$ attached to $h$ and $h \cdot w = w_1$. Then for every $n \in \mathbb{N}$ and every $y \in H^n(H, \mathbb{A}_F^\times)$, the image of $y$ under the map induced by the pair (inclusion $H \cap D_{w_1} \le H$, $\mathrm{pr}^H_{w_1}$) equals the image under the map induced by $(c_h, T_h)$ of the image of $y$ under the map induced by (inclusion $H \cap D_w \le H$, $\mathrm{pr}^H_w$).
--
--   This is the statement that the local coordinate maps of $H^n(H, \mathbb{A}_F^\times)$ at two places in the same $H$-orbit differ only by the conjugation isomorphism, so that a sum over places may be replaced by a sum over orbits with the appropriate index; it is the version for a general subgroup $H$ of the corresponding statement for $H = G$. It is used in the computation of the cohomology of the $S$-idèles in the form [`M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem M4aHerbrand.map_prH_eq_map_map_prH_of_smul_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F))

    (prH : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H))
          (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hprH : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ),
      (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (w w₁ : HeightOneSpectrum (𝓞 F)) (h : ↥H) (hh : (h : F ≃ₐ[E] F) • w = w₁)
    (ch : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)))
    (hch : ∀ x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)),
      ((ch x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F))
    (Th : Rep.res ch (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ))
    (hTh : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (Th.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport (h : F ≃ₐ[E] F) hh (x : w.adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) n) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ H)) (prH w₁) n).hom y =
      (groupCohomology.map ch Th n).hom
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (prH w) n).hom y) := by sorry
