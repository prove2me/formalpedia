-- Prove2me | Theorems.Thm_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
-- name    : NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/146d4193-ed4c-5d7b-86d3-8e6dc5df75fa
-- title:
--   Local component at w ∤ S of an S-unit class vanishes
-- statement:
--   Let $S$ be a finite set of rational primes, and let $L \subseteq F$ be intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$, both finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$ and with $F$, viewed as the intermediate field `levelField L F hLF` of $\overline{\mathbb{Q}}/L$, Galois over $L$; assume $F$ is unramified outside $S$, i.e. $F/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F$. Let $\iota$ be a monoid homomorphism from $\mathrm{Gal}(F/L)$ to the quotient of $L$'s fixing subgroup by the preimage of $F$'s fixing subgroup, satisfying $\iota(\mathrm{levelGal}(g)) = \bar g$ for all $g$ in $L$'s fixing subgroup. Let $\varphi$ be a morphism, bijective on underlying modules, from the $\iota$-restriction of the $(F.\mathrm{fixingSubgroup})$-invariants quotient representation of `sUnitsMaxRep S L` to the $S$-unit representation `sUnitsRep` of $\mathrm{Gal}(F/L)$ for the finite set of primes of $\mathcal{O}_L$ above $S$, whose underlying map preserves values in $\overline{\mathbb{Q}}$. Let $D$ be a Galois descent datum for the adèle ring of $F$ over $L$ (a continuous action by ring automorphisms compatible with $\mathrm{algebraMap}$), and assume the ambient multiplicative-distributive action of $\mathrm{Gal}(F/L)$ on the idèles $(\mathbb{A}_F)^\times$ agrees with the one induced by $D$. Let $j$ be a morphism from the $S$-unit representation to the idèle-unit representation realising the principal-idèle map, i.e. $j(y)$ is the image of the $S$-unit value of $y$ under $\mathrm{algebraMap}$, and for each finite place $w$ of $F$ let $\mathrm{prG}\,w$ be a morphism from the restriction of the idèle-unit representation to the decomposition subgroup of $w$ into $(F_w)^\times$, realising the $w$-component `finPart w`. Then for every $2$-cocycle $f$ of the quotient group with values in the invariants quotient of `sUnitsMaxRep S L`, and every height-one prime $w$ of $\mathcal{O}_F$ whose contraction along $\mathcal{O}_L \to \mathcal{O}_F$ differs from every prime of $\mathcal{O}_L$ above $S$, the degree-$2$ cohomology class of $f$, pushed forward by $\varphi$ followed by $j$ along $\iota$ and then restricted to the decomposition group of $w$ and mapped by $\mathrm{prG}\,w$, is $0$ in $H^2(D_w, (F_w)^\times)$.
--
--   This is the local triviality, away from $S$, of the idèle class attached to a $2$-cocycle with $S$-unit values: the values are $w$-units and $F/L$ is unramified at $w$, so the $w$-component factors through cohomology of the local integral units, which is trivial. It supplies the support hypothesis used in the computation of Brauer local invariants, and is cited by [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv) and [`NumberField.LevelArith.injective_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.injective_of_isBrauerLocalInv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand
open IsDedekindDomain

theorem NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)

    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))

    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)))
    (hw : ∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom
      ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := by sorry
