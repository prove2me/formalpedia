-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
-- name    : NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/cfb24cf9-5fe4-5263-9647-3bbd586df9d6
-- title:
--   Invariant maximal S-units as the S-units of F
-- statement:
--   Let $S$ be a finite set of rational primes and let $L \le F$ be intermediate fields of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` over $\mathbb{Q}$, both finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$ and with $F$, viewed via `levelField L F hLF` as an intermediate field of $\overline{\mathbb{Q}}$ over $L$, Galois over $L$; assume moreover `F.IsUnramifiedOutside S`, i.e. $F$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ (the image of `A.inertiaSubgroup` inside the decomposition subgroup) lies in the fixing subgroup of $F$. Write $\Gamma_L =$ `L.fixingSubgroup` and $U_F$ for the preimage of `F.fixingSubgroup` in $\Gamma_L$. Then there exist a group homomorphism $\iota\colon \mathrm{Gal}(F/L) \to \Gamma_L/U_F$ with $\iota(\mathrm{levelGal}(g)) = gU_F$ for all $g \in \Gamma_L$, and a morphism $\varphi$ of $\mathbb{Z}$-linear representations of $\mathrm{Gal}(F/L)$ from the $U_F$-invariants of the maximal $S$-unit module `sUnitsMaxRep S L` (a $\Gamma_L$-submodule of `Additive (AlgebraicClosure ℚ)ˣ`), regarded as a representation of $\Gamma_L/U_F$ and restricted along $\iota$, to the $S$-unit representation `sUnitsRep` of $\mathrm{Gal}(F/L)$ on the $S$-units of $F$ for the finite set of height-one primes of $\mathcal{O}_L$ lying over the primes in $S$, such that the underlying map of $\varphi$ is bijective and, for every $x$, the image in $\overline{\mathbb{Q}}$ of the unit of $F$ attached to $\varphi(x)$ equals the image in $\overline{\mathbb{Q}}$ of the unit of $\overline{\mathbb{Q}}$ underlying $x$.
--
--   This packages the classical identification of the $\Gamma_F$-invariants of the module of $S$-units of $\overline{\mathbb{Q}}$ with the $S$-units of the finite layer $F$, together with the identification $\Gamma_L/U_F \cong \mathrm{Gal}(F/L)$, in the equivariant form used later in the finite-layer Hasse principle and in the definition of the Brauer local invariant character; it is cited by the results on vanishing of the relevant $H^2$ classes and on local invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand
open NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S) :
    ∃ (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
      (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
        NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      Function.Bijective φ.hom ∧
      ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by sorry
