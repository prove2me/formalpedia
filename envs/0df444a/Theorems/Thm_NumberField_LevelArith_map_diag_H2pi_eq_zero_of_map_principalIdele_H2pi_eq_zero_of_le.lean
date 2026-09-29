-- Prove2me | Theorems.Thm_NumberField_LevelArith_map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le
-- name    : NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/92a213ca-3bd8-5487-8b39-ddb023a185e7
-- title:
--   Vanishing S-idèle class of a restricted layer 2-cocycle
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L \le L' \le F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, all finite over $\mathbb{Q}$, with $F/\mathbb{Q}$ normal, $F$ Galois (resp. normal) over $L$ and over $L'$ when regarded through `levelField` as an extension of $L$ (resp. $L'$) by extension of scalars, and with $F$ unramified outside $S$ in the sense that $F/\mathbb{Q}$ is finite and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $q$ among its nonunits, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F$. For the base $L$ one is given: a homomorphism $\iota$ from $\mathrm{Gal}(F/L)$ to $\Gamma_L/\Gamma_F$ (the fixing subgroup of $L$ modulo the pullback of that of $F$) inverting `levelGal`; a morphism $\varphi$, bijective on underlying groups and compatible with the values in $\overline{\mathbb{Q}}$, from the $\iota$-restriction of the representation of $\Gamma_L/\Gamma_F$ on the $\Gamma_F$-invariants of the $S$-units of $\overline{\mathbb{Q}}$ to the $S$-unit representation of $\mathrm{Gal}(F/L)$ for the places of $L$ over $S$; a Galois descent $D$ of the adèle ring of $F$ over $L$, namely a continuous action of $\mathrm{Gal}(F/L)$ by ring automorphisms compatible with the structure map, inducing the given multiplicative-distributive action on idèle units; and a morphism $j$ into the idèle units which on values is the principal-idèle embedding. For the base $L'$ one is given the analogous $\iota'$ and $\varphi'$. Finally let $f$ be a $2$-cocycle of $\Gamma_L/\Gamma_F$ in the $\Gamma_F$-invariant $S$-units whose class $H^2\pi(f)$ is killed by the map on $H^2$ induced by $\iota$ and $\varphi$ followed by $j$, and let $f'$ be a $2$-cocycle over $L'$ whose values in $\overline{\mathbb{Q}}$ agree with those of $f$ whenever the arguments come from elements of $\Gamma_{L'}$ and $\Gamma_L$ inducing the same automorphism of $\overline{\mathbb{Q}}$. Then the class $H^2\pi(f')$ is killed by the map on $H^2$ induced by $\iota'$ and by $\varphi'$ followed by the diagonal morphism [`NumberField.SIdele.diag`](def/NumberField_SIdeleModule.html#L91) from the $S$-units of $F$ over $L'$ into the $S$-idèle module of $F$ over $L'$.
--
--   This transports the vanishing of the idèle class of a layer $2$-cocycle from the base $L$ to the larger base $L'$, and converts it from a statement about the full idèle units to one about the $S$-idèle module. In this form it is exactly the hypothesis required by the finite-layer Hasse principle with capitulation, and it is used in the inflation step for continuous $H^2$ of $S$-units along the tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le
    (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L'] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L' ↥(levelField L' F hL'F)] [Normal ↥L' ↥(levelField L' F hL'F)] (hF : F.IsUnramifiedOutside S)

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
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

    (ι' : (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) →* (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))
    (hι' : ∀ g : ↥L'.fixingSubgroup, ι' (levelGal L' F hL'F g) = (g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (φ' : Rep.res ι' ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S))
    (hφ' : Function.Bijective φ'.hom)
    (hφval' : ∀ x, ((NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) (φ'.hom x) : ↥(levelField L' F hL'F)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L' (x.1 : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hx : (groupCohomology.map ι (φ ≫ j) 2) (H2π _ f) = 0)
    (f' : cocycles₂ ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)))
    (hff' : ∀ (g h : ↥L'.fixingSubgroup) (g₀ h₀ : ↥L.fixingSubgroup),
      ((g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((h₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((sUnitsMaxRep.val S L' ((f' ((g : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)), (h : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L ((f ((g₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h₀ : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :
    (groupCohomology.map ι' (φ' ≫ NumberField.SIdele.diag ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S)) 2) (groupCohomology.H2π _ f') = 0 := by sorry
