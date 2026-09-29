-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
-- name    : NumberField.LevelArith.exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/03a1027c-7012-586f-87c8-b096cbbbf660
-- title:
--   Invariants of the maximal S-units are the S-units of F
-- statement:
--   Fix a finite set $S$ of rational primes and two intermediate fields $L \le F$ of $\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, both finite over $\mathbb{Q}$, with $F/\mathbb{Q}$ normal and with $F$, regarded through `levelField L F hLF` as an intermediate field of $\overline{\mathbb{Q}}/L$, normal over $L$; assume further `F.IsUnramifiedOutside S`, i.e. $F$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ is contained in the fixing subgroup of $F$. Let `sUnitsMaxRep S L` be the $\mathbb{Z}[L.fixingSubgroup]$-module given by the subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^\times$ written additively, and form its invariants under the normal subgroup $F.\mathrm{fixingSubgroup} \cap L.\mathrm{fixingSubgroup}$ (the comap of the former along the inclusion of the latter), a representation of the quotient group. The assertion is that there is an isomorphism $e$ of additive groups from this invariants module onto [`NumberField.SUnits.sUnitsRep`](def/NumberField_SUnitsModule.html#L52) of $L \subseteq$ `levelField L F hLF` at the finite set of height-one primes of $\mathcal{O}_L$ lying over the primes in $S$, such that: first, $e$ preserves underlying elements, i.e. for every $x$ the element of $\overline{\mathbb{Q}}$ underlying the unit $\mathrm{Additive.toMul}\,(e\,x)_1$ of `levelField L F hLF` coincides with the element of $\overline{\mathbb{Q}}$ underlying `sUnitsMaxRep.val S L x.1`; and second, $e$ is equivariant along `levelGal L F hLF`, namely for all $g$ in $L.\mathrm{fixingSubgroup}$ and all $x$, applying $e$ after the action of the class of $g$ in the quotient equals the action of `levelGal L F hLF g` after $e$.
--
--   This is the module half of the identification of the $\Gamma_F$-invariants of the $S$-units of the maximal $S$-ramified extension with the $S$-units $\mathcal{O}_{F,S}^\times$ of $F$, as a module over $\mathrm{Gal}(F/L)$, the group half being the surjectivity and kernel computation for `levelGal`. It is used in the cohomological arguments over level fields, in particular in the statements on $H^2$ of the $S$-units module and on level coboundaries that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ F] [Normal ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S) :
    ∃ e : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))
        ≃+ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      (∀ x, (((Additive.toMul ((e x).1) : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) =
        ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ∧
      ∀ (g : ↥L.fixingSubgroup) (x),
        e (((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)).ρ
            (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) x) =
          (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ (levelGal L F hLF g) (e x) := by sorry
