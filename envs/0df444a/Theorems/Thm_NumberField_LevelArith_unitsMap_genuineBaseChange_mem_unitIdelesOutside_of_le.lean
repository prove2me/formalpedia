-- Prove2me | Theorems.Thm_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
-- name    : NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/9b8f4ea2-2418-5b9e-8241-803c39d17ff3
-- title:
--   Genuine base change preserves S-idèles and S-units in level towers
-- statement:
--   Fix a finite set $S$ of rational primes and intermediate fields $L\le F$ and $L\le L_1\le F_1$, $F\le F_1$, of $\overline{\mathbb Q}/\mathbb Q$, all four finite over $\mathbb Q$. Write $K$ for `levelField L F hLF`, i.e. $F$ regarded as an intermediate field of $\overline{\mathbb Q}$ over $L$ via `IntermediateField.extendScalars`, and likewise $K_1$ for `levelField L₁ F₁ hL₁F₁`. Assume given an algebra structure of $K$ over $K_1$ whose structure map is the identity on underlying elements of $\overline{\mathbb Q}$ (hypothesis `halg`). Two assertions are made together. First, if a unit $x$ of the adèle ring of $K$ is a local unit at every height-one prime $v$ of $\mathcal O_K$ whose restriction $v\cap\mathcal O_L$ does not belong to the finite set `placesOverPrimesFinset ↥L S` of primes of $\mathcal O_L$ attached to $S$ — that is, the finite components of $x$ and of $x^{-1}$ at such $v$ both lie in $\mathcal O_{K_v}$, no condition being imposed at the infinite places — then the image of $x$ under the ring homomorphism $\beta$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange`](def/M4aHerbrand_GenuineDescent.html#L87) from the adèles of $K$ to those of $K_1$ satisfies the same condition for $K_1$, with primes restricted to $\mathcal O_{L_1}$ and tested against `placesOverPrimesFinset ↥L₁ S`. Second, every element of the $\mathbb Z[\,K\simeq_L K\,]$-representation [`NumberField.SUnits.sUnitsRep ↥L ↥K (placesOverPrimesFinset ↥L S)`](def/NumberField_SUnitsModule.html#L52) has its associated unit in $K^\times$ mapped by the inclusion $K\to K_1$ to the unit associated with some element of `sUnitsRep ↥L₁ ↥K₁ (placesOverPrimesFinset ↥L₁ S)`.
--
--   This is the compatibility, along a tower of level fields, of the two basic $S$-objects: the group of idèles that are units outside the primes above $S$, and the module of $S$-units, under the adèle base change map. It is used in the level-arithmetic step by [`NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d`](thm.html#NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d) and [`NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le`](thm.html#NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le), where coboundary relations between $S$-idèles and $S$-units are transported to a larger level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le.lean

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
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
    (S : Finset Nat.Primes)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]
    (L₁ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F₁ : L₁ ≤ F₁) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F₁]
    [Algebra ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)]
    (halg : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) :
    (∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁) {w | w.under (𝓞 ↥L₁) ∈ (placesOverPrimesFinset ↥L₁ S)}) ∧
    (∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), ∃ x' : (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)),
      NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) x' = Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) : ↥(levelField L F hLF) →* ↥(levelField L₁ F₁ hL₁F₁)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)) := by sorry
