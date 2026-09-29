-- Prove2me | Theorems.Thm_NumberField_LevelArith_map_principalIdele_H2pi_eq_zero_of_le
-- name    : NumberField.LevelArith.map_principalIdele_H2pi_eq_zero_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c51da995-0d3a-5593-973b-64f1110b0463
-- title:
--   Vanishing idèle class transfers from base L to L'
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L \le L' \le F$ of $\overline{\mathbb Q}/\mathbb Q$ (the inclusions $L\le L'$, $L'\le F$, $L\le F$ being given), all finite over $\mathbb Q$, with $F$ normal over $\mathbb Q$, together with Galois/normality hypotheses for $F$ regarded as an extension of $L$ and of $L'$ via `levelField` (extension of scalars), and the hypothesis `F.IsUnramifiedOutside S`: $F$ is finite over $\mathbb Q$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb Q$, pushed into the automorphism group, lies in the fixing subgroup of $F$. On the $L$-side one is given: a monoid homomorphism $\iota$ from $\mathrm{Gal}(F_L/L)$ to $\mathrm{Gal}(\overline{\mathbb Q}/L)/\mathrm{Gal}(\overline{\mathbb Q}/F)$ (the latter as the comap of $F$'s fixing subgroup) which, by $h\iota$, composes with `levelGal` to the quotient map; a morphism $\varphi$ of representations from the $\iota$-restriction of the $\mathrm{Gal}(\overline{\mathbb Q}/F)$-invariants quotient of the maximal $S$-unit representation `sUnitsMaxRep S L` to the $S$-unit representation of $F_L/L$ at the places above $S$, bijective on underlying maps and compatible with the $S$-unit values inside $\overline{\mathbb Q}$; an idèle Galois descent datum $D$ on the adèles of $F_L$ (a homomorphism from $\mathrm{Gal}(F_L/L)$ to ring automorphisms of the adèle ring, compatible with the structure map from $F_L$ and continuous), a multiplicative distributive action on the adelic units pinned to $D$'s induced action, and a morphism $j$ from the $S$-unit representation to the adelic units pinned to the principal-idèle map. The same data $\iota',\varphi',D',j'$ with the same pinning hypotheses is given on the $L'$-side. Finally, $f$ is a $2$-cocycle of $\mathrm{Gal}(\overline{\mathbb Q}/L)/\mathrm{Gal}(\overline{\mathbb Q}/F)$ with values in the invariants quotient over $L$ whose class satisfies $(\mathrm{map}\ \iota\ (\varphi \text{ followed by } j)\ 2)(H^2\pi\, f) = 0$, and $f'$ is a $2$-cocycle on the $L'$-side whose values agree with those of $f$ in $\overline{\mathbb Q}$ whenever the arguments are represented by the same automorphisms of $\overline{\mathbb Q}$. The conclusion is that $(\mathrm{map}\ \iota'\ (\varphi' \text{ followed by } j')\ 2)(H^2\pi\, f') = 0$.
--
--   This is the compatibility, between two base fields $L \le L'$ inside a common $F$, of the statement that the idèle class attached to an $S$-unit $2$-cocycle vanishes: the vanishing over $L$ forces the vanishing over $L'$ for any cocycle with the same values. It feeds the diagonal form of the same transfer, [`NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le`](thm.html#NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le), and the proof uses the uniqueness of an idèle Galois descent datum together with the surjectivity and kernel computation for `levelGal`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_map_principalIdele_H2pi_eq_zero_of_le.lean

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

theorem NumberField.LevelArith.map_principalIdele_H2pi_eq_zero_of_le
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

    (D' : IdeleGaloisDescent (𝓞 ↥(levelField L' F hL'F)) ↥L' ↥(levelField L' F hL'F))
    [MulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ]
    (hactI' : ∀ (g : ↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (x : (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ), g • x = D'.unitsAct g x)
    (j' : NumberField.SUnits.sUnitsRep ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L' F hL'F) ≃ₐ[↥L'] ↥(levelField L' F hL'F)) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))ˣ)
    (hj' : ∀ y, Additive.toMul (j'.hom y) =
      Units.map (algebraMap ↥(levelField L' F hL'F) (AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F)) : ↥(levelField L' F hL'F) →* AdeleRing (𝓞 ↥(levelField L' F hL'F)) ↥(levelField L' F hL'F))
        (NumberField.SUnits.val ↥L' ↥(levelField L' F hL'F) (placesOverPrimesFinset ↥L' S) y))

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
    (groupCohomology.map ι' (φ' ≫ j') 2) (groupCohomology.H2π _ f') = 0 := by sorry
