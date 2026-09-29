-- Prove2me | Theorems.Thm_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
-- name    : M4aHerbrand.eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/bb2f6d2e-e6e5-5e67-848c-eab393eb6b4e
-- title:
--   Vanishing at chosen places kills idèle cohomology classes
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and write $G = \mathrm{Gal}(F/E)$. Let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$: a group homomorphism from $G$ to the ring automorphisms of $\mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$ which is compatible with the structure map from $F$ and continuous in each $g$. Assume a multiplicative-distributive action of $G$ on the units $(\mathrm{AdeleRing}\,(\mathcal{O}_F)\,F)^\times$ which, by `hactI`, agrees with the action induced by $D$ on units; let $A$ denote the resulting $\mathbb{Z}[G]$-representation. For each height-one prime $w$ of $\mathcal{O}_F$ let $\mathrm{pr}\,w$ be a morphism of representations of the decomposition subgroup $\mathrm{decomp}\,E\,F\,w$ (the stabiliser of the valuation subring of $w$) from the restriction of $A$ to that subgroup to $(F_w)^\times$, which by `hpr` is given on elements by the $w$-component `finPart w`; for each infinite place $v$ of $F$ let $\mathrm{prInf}\,v$ be a morphism of representations of $\mathrm{decomp}\,E\,F\,v$ (the stabiliser of $v$) from the restriction of $A$ to the representation on $(F_v)^\times$, which by `hprInf` is given by the infinite part of an idèle followed by evaluation at $v$. Let $n \in \mathbb{N}$ and $x \in H^{n+1}(G, A)$. If for every height-one prime $v$ of $\mathcal{O}_E$ the map on $H^{n+1}$ induced by the inclusion of the decomposition subgroup together with $\mathrm{pr}$ at the chosen prime above $v$ annihilates $x$, and likewise for every infinite place $v$ of $E$ at the chosen infinite place above $v$, then $x = 0$.
--
--   This is the injectivity half of the description of the cohomology of the idèle group as a sum of local contributions, in the form that a class in $H^{n+1}(\mathrm{Gal}(F/E), \mathbb{I}_F^\times)$ vanishes as soon as its local coordinates vanish at one chosen place of $F$ above each place of $E$; the reduction to a single place in each Galois orbit is what makes the hypotheses indexed by places of $E$ rather than of $F$. It is used in the construction of local inverses for idèle classes, in [`NumberField.IdeleLocalInv.exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv`](thm.html#NumberField.IdeleLocalInv.exists_pow_smul_eq_zero_and_map_pi_eq_zero_and_hasLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles.lean

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
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem M4aHerbrand.eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (pr : ∀ w : HeightOneSpectrum (𝓞 F), Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w).adicCompletion F)ˣ)
    (hpr : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (pr w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (hprInf : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (n : ℕ) (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = 0)
    (hinf : ∀ v : InfinitePlace E,
      (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (prInf (NumberField.ArchIdele.above E F v)) (n + 1)).hom x = 0) :
    x = 0 := by sorry
