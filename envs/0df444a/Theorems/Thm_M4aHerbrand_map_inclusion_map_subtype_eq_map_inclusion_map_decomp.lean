-- Prove2me | Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp
-- name    : M4aHerbrand.map_inclusion_map_subtype_eq_map_inclusion_map_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/0fa27abc-5214-53ae-bd7c-d574a63a76c3
-- title:
--   Compatibility of local W-coordinate maps under restriction
-- statement:
--   Let $E \subseteq M$ be number fields with $M/E$ Galois, and let the Galois group $G = M \simeq_{\mathrm{alg}[E]} M$ act multiplicatively and distributively on the unit group $(\mathbb{A}_M)^\times$ of the adèle ring of $M$; write $A$ for the associated $\mathbb{Z}$-linear representation `Rep.ofMulDistribMulAction` of $G$ on the additive group underlying $(\mathbb{A}_M)^\times$. Fix a subgroup $S \le G$ and a height-one prime $W$ of $\mathcal{O}_M$, and let $D =$ [`NumberField.PlaceDecomp.decomp E M W`](def/NumberField_PlaceDecompositionAction.html#L82) be the decomposition subgroup of $E$ in the valuation subring of the $W$-adic valuation of $M$. Assume given two morphisms of representations: $\mathrm{prH}$, from the restriction of $A$ along $S \cap D \hookrightarrow S \hookrightarrow G$ to the restriction along $S \cap D \hookrightarrow D$ of the representation of $D$ on $(M_W)^\times$, and $\mathrm{prM}$, from the restriction of $A$ along $D \hookrightarrow G$ to that same representation of $D$ on $(M_W)^\times$; both are assumed, on each unit idèle $x$, to be given by `finPart W x`, the $W$-th coordinate of the finite part of $x$ in $(M_W)^\times$ (via `Additive.ofMul`). Then for every $n \in \mathbb{N}$ and every class $x \in H^n(G, A)$, applying `groupCohomology.map` along $S \cap D \le S$ with coefficient map $\mathrm{prH}$ to the restriction of $x$ to $S$ yields the same element as applying `groupCohomology.map` along $S \cap D \le D$ with identity coefficient map to the image of $x$ under `groupCohomology.map` along $D \hookrightarrow G$ with coefficient map $\mathrm{prM}$; both lie in $H^n(S \cap D, (M_W)^\times)$.
--
--   This is the functoriality of group cohomology in the pair (group, coefficient module) applied to the $W$-coordinate map on idèles: restricting a global class first to $S$ and then taking the $W$-coordinate agrees with taking the $W$-coordinate on the decomposition group $D$ and then restricting to $S \cap D$. It serves as bookkeeping that transfers computations carried out on the full decomposition group at $W$ to coordinates of classes restricted to a subgroup $S$, and is used in [`M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.map_inclusion_map_subtype_eq_map_inclusion_map_decomp
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (S : Subgroup (M ≃ₐ[E] M)) (W : HeightOneSpectrum (𝓞 M))
    (prH : Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S))
          (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))
    (hprH : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prH.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (n : ℕ) (x : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) n) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ S)) prH n).hom
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) n).hom x) =
      (groupCohomology.map (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : S ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))) n).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM n).hom x) := by sorry
