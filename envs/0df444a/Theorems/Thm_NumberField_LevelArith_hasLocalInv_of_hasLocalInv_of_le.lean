-- Prove2me | Theorems.Thm_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
-- name    : NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1f9c58f2-71f0-5b9d-a245-cf0a5cfbf6b2
-- title:
--   Local invariants unchanged on passing to a larger S-level
-- statement:
--   Fix a finite set $S$ of rational primes and a number field $L\subset\overline{\mathbb{Q}}$ (an intermediate field of $\mathbb{Q}$ in `AlgebraicClosure ℚ`, finite over $\mathbb{Q}$). Let $F$ and $F''$ be intermediate fields containing $L$, each finite over $\mathbb{Q}$ and normal over $\mathbb{Q}$, with $F$ viewed over $L$ as `levelField L F hLF` (and likewise for $F''$) Galois over $L$, each satisfying `IsUnramifiedOutside S`, i.e. finite over $\mathbb{Q}$ and such that for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field; assume $F\le F''$. At each of the two levels one is given: a monoid homomorphism $\iota$ from $\mathrm{Gal}(F/L)$ to $\Gamma_L/\Gamma_F$ (the quotient of $L$'s fixing subgroup by the intersection with $F$'s) which composed with `levelGal` is the canonical projection; an isomorphism $\varphi$ of representations, with bijective underlying map, from the restriction along $\iota$ of the $\Gamma_F$-invariants quotient of the $S$-unit module `sUnitsMaxRep S L` inside $\overline{\mathbb{Q}}^{\times}$ onto `sUnitsRep` of $F/L$ for the places of $L$ over $S$, compatible with the underlying values in $\overline{\mathbb{Q}}$; an idèle Galois descent datum $D$ (a homomorphism $\mathrm{Gal}(F/L)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_F)$ continuous and extending the action on $F$) whose induced action on $\mathbb{A}_F^{\times}$ is the ambient one; and a morphism $j$ from the $S$-unit representation to $\mathbb{A}_F^{\times}$ given by the principal-idèle map. Finally, let $f$ and $f''$ be $2$-cocycles of $\Gamma_L/\Gamma_F$, resp. $\Gamma_L/\Gamma_{F''}$, valued in the corresponding invariants, taking equal values in `sUnitsMaxRep S L` on all pairs of images of elements of $\Gamma_L$, and let $v$ be a height-one prime of $\mathcal{O}_L$ and $t\in\mathbb{Q}/\mathbb{Z}$. The assertion is that `HasLocalInv` for the class obtained from $f$ by $\varphi$ followed by $j$ and the map of cohomology along $\iota$ in degree $2$, at $v$ with value $t$, implies the same for $f''$ at the level $F''$. Here `HasLocalInv` of a class $x$ at $v$ with value $t$ asserts the existence of the local-component morphisms to the completions computing finite parts, of a place $w$ of the level field contracting to $v$, of a prime $q$ in $w$, of a realisation of $F_w$ as a finite extension of $\mathbb{Q}_q$ with compatible decomposition-group action and base field, of a local fundamental class $u'$ there, and of $n\in\mathbb{Z}$ with the restriction of $x$ to $H^2(D_w,F_w^{\times})$ equal to $n\cdot u'$ and $t=n/|D_w|$ in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the compatibility of the local invariant of an idèle class with inflation from one Galois $S$-level to a larger one. It is what makes the local-invariant map on the second cohomology of the $S$-unit module independent of the level used to present a class, and it is cited by [`NumberField.LevelArith.eq_of_hasBrauerLocalInvAt`](thm.html#NumberField.LevelArith.eq_of_hasBrauerLocalInvAt) and [`NumberField.LevelArith.hasBrauerLocalInvAt_add`](thm.html#NumberField.LevelArith.hasBrauerLocalInvAt_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF'' : L ≤ F'') [FiniteDimensional ℚ ↥F''] [Normal ℚ ↥F''] [IsGalois ↥L ↥(levelField L F'' hLF'')] (hF'' : F''.IsUnramifiedOutside S)
    (hFF'' : F ≤ F'')

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (ι'' : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι'' (levelGal L F'' hLF'' g) = (g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ'' : Rep.res ι'' ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ''.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (φ''.hom x) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (_ : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))
    (D'' : IdeleGaloisDescent (𝓞 ↥(levelField L F'' hLF'')) ↥L ↥(levelField L F'' hLF''))
    [MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ]
    (hactI'' : ∀ (g : ↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (x : (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ), g • x = D''.unitsAct g x)
    (j'' : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)
    (_ : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))
        (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (f'' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hff'' : ∀ g h : ↥L.fixingSubgroup,
      ((f'' ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
        = ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L))
    (v : HeightOneSpectrum (𝓞 ↥L)) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v t) :
    NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F'' hLF'') D'' hactI'' ((groupCohomology.map ι'' (φ'' ≫ j'') 2) (H2π _ f'')) v t := by sorry
