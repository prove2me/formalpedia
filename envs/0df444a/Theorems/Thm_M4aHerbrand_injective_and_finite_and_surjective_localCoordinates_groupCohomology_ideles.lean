-- Prove2me | Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
-- name    : M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/974616a7-723d-5242-a122-f59c7c6fe192
-- title:
--   Local coordinates on idèle cohomology: injectivity, finiteness, surjectivity
-- statement:
--   Let $F/E$ be a Galois extension of number fields with group $G=\mathrm{Gal}(F/E)$, and let $D$ be an `IdeleGaloisDescent` datum for $\mathbb{A}_F=$ `AdeleRing (𝓞 F) F`, i.e. a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$ extending the action on $F$ through the structure map and continuous for each $g$. The given multiplicative action of $G$ on $\mathbb{A}_F^\times$ is assumed (hypothesis `hactI`) to be the one induced by $D$ on units, so that $\mathbb{A}_F^\times$, written additively, is a $\mathbb{Z}$-linear $G$-representation. For each prime $w$ of $\mathcal{O}_F$ one is given a morphism `pr w` from the restriction of this representation to the decomposition subgroup of $w$ (the decomposition subgroup of the valuation subring of $w$) to the units of the completion $F_w$, pinned by `hpr` to be the $w$-component map `finPart w`; likewise for each infinite place $v$ of $F$ a morphism `prInf v` to the units of $F_v$, over the stabiliser of $v$, pinned by `hprInf` to be evaluation of the infinite part at $v$. Fix $n$. Then, with local coordinates at a place defined as the composite of restriction to the decomposition group with the above projections in degree $n+1$: (i) a class $x \in H^{n+1}(G,\mathbb{A}_F^\times)$ all of whose finite and infinite local coordinates vanish is zero; (ii) for each $x$ the set of primes $w$ with nonzero coordinate is finite; (iii) for every finite set $T$ of primes of $\mathcal{O}_E$, every family $(y_v)$ of classes in $H^{n+1}(D_{w(v)}, F_{w(v)}^\times)$ indexed by primes $v$ of $\mathcal{O}_E$, where $w(v)$ is the chosen prime of $\mathcal{O}_F$ above $v$, and every family $(y^\infty_v)$ of classes in $H^{n+1}(D_{w(v)}, F_{w(v)}^\times)$ at the chosen infinite places $w(v)$ above the infinite places $v$ of $E$, there is a class $x$ whose coordinate at $w(v)$ equals $y_v$ for $v \in T$, vanishes for $v \notin T$, and whose infinite coordinate at $w(v)$ equals $y^\infty_v$ for every infinite place $v$ of $E$.
--
--   This is the Shapiro-type description of the cohomology of the idèle group of a finite Galois extension: in degree $n+1$ the total local-coordinate map identifies $H^{n+1}(G,\mathbb{A}_F^\times)$ with the direct sum over the places $v$ of $E$ of the local groups $H^{n+1}(D_{w(v)}, F_{w(v)}^\times)$, here stated as injectivity, finiteness of support, and surjectivity with prescribed support. It is used in the project's computations with idèle and idèle class cohomology, in particular in the Herbrand-quotient arguments that reduce global statements to local ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles.lean

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

theorem M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
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
    (n : ℕ) :
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      (∀ w : HeightOneSpectrum (𝓞 F), (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x = 0) →
      (∀ v : InfinitePlace F, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) (n + 1)).hom x = 0) → x = 0) ∧
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      {w : HeightOneSpectrum (𝓞 F) | (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x ≠ 0}.Finite) ∧
    (∀ (T : Finset (HeightOneSpectrum (𝓞 E)))
      (y : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology
        (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (((NumberField.PlaceAbove.above E F v)).adicCompletion F)ˣ) (n + 1))
      (yinf : ∀ v : InfinitePlace E, groupCohomology (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) (n + 1)),
      ∃ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
        (∀ v ∈ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = y v) ∧
        (∀ v ∉ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = 0) ∧
        (∀ v : InfinitePlace E, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (prInf (NumberField.ArchIdele.above E F v)) (n + 1)).hom x = yinf v)) := by sorry
