-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply
-- name    : M4aHerbrand.exists_hom_res_inf_decomp_ideles_adicCompletion_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/12fd1c51-330e-57c5-803d-0e71eebd6291
-- title:
--   Local coordinate maps at w as H∩ D_w-morphisms
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra and $F/E$ Galois, and let $D$ be an idèle Galois descent datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism $\mathrm{act}$ from $\mathrm{Gal}(F/E)$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ of $\mathcal{O}_F$ over $F$, each $\mathrm{act}(g)$ continuous and compatible with the structure map $F \to \mathbb{A}_F$ in the sense that $\mathrm{act}(g)(\iota x) = \iota(g x)$. Assume given a multiplicative-distributive action of $\mathrm{Gal}(F/E)$ on the unit group $\mathbb{A}_F^\times$ which, by hypothesis `hactI`, agrees for every $g$ and $x$ with the action `D.unitsAct` obtained by applying $\mathrm{act}(g)$ to units. Let $H$ be a subgroup of $\mathrm{Gal}(F/E)$. The assertion is that there exists a family $\mathrm{prH}$, indexed by the height-one primes $w$ of $\mathcal{O}_F$, of morphisms of $\mathbb{Z}$-linear representations of $H \sqcap \mathrm{decomp}(w)$ — where $\mathrm{decomp}(w)$ is the decomposition subgroup of the valuation subring of the $w$-adic valuation of $F$ — from the restriction along $H \sqcap \mathrm{decomp}(w) \le H \le \mathrm{Gal}(F/E)$ of the additive representation attached to $\mathbb{A}_F^\times$, to the restriction along $H \sqcap \mathrm{decomp}(w) \le \mathrm{decomp}(w)$ of the additive representation attached to $(F_w)^\times$, such that for all $w$ and all $x \in \mathbb{A}_F^\times$ the underlying map sends $x$ to `finPart w x`, the $w$-component of the finite part of $x$.
--
--   These are the value-pinned local coordinate maps $\mathrm{pr}_w\colon \mathbb{I}_F \to F_w^\times$ of the cohomology of idèles, in the form of morphisms of modules over $H \cap D_w$ for an arbitrary subgroup $H$ of the Galois group (the case $H = \mathrm{Gal}(F/E)$ being the decomposition-group version). They are the input data for the Shapiro-type decomposition of the cohomology of the idèle module at a subgroup, and the statement is cited in the divisibility result [`M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_res_inf_decomp_ideles_adicCompletion_apply.lean

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

theorem M4aHerbrand.exists_hom_res_inf_decomp_ideles_adicCompletion_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ prH : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H))
            (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
          Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ NumberField.PlaceDecomp.decomp E F w))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ),
      ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x) := by sorry
