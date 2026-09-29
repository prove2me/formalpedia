-- Prove2me | Theorems.Thm_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
-- name    : NumberField.LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/59c74bbe-962d-5c15-9248-4577877813b2
-- title:
--   Unramifiedness off S of the layer F_L over L
-- statement:
--   Let $S$ be a finite set of rational primes and let $L \le F$ be intermediate fields of $\overline{\mathbb Q}/\mathbb Q$ inside `AlgebraicClosure ℚ`, both finite over $\mathbb Q$. Assume `F.IsUnramifiedOutside S`, that is: $F$ is finite over $\mathbb Q$ and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$ (so $A$ lies over $q$), the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$, transported along the inclusion of the decomposition subgroup, lies in the fixing subgroup of $F$. Let $w$ be a height-one prime of the ring of integers of `levelField L F hLF`, i.e. of $F$ regarded as an intermediate field of $\overline{\mathbb Q}/L$ via `IntermediateField.extendScalars`, and suppose that the prime $w \cap \mathcal O_L =$ `w.under (𝓞 ↥L)` does not belong to `placesOverPrimesFinset ↥L S`, the finite set of height-one primes of $\mathcal O_L$ lying over a prime of $S$. Then `Ideal.ramificationIdx'` of $w$ over $w \cap \mathcal O_L$ equals $1$.
--
--   This is the Dedekind-theoretic form of the statement that the layer $F_L$ is unramified over $L$ away from $S$, phrased for a single finite place of $F_L$ whose restriction to $L$ avoids $S$. It supplies the ramification hypothesis used in the cohomological computations with $S$-idèles, and is cited by [`NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele`](thm.html#NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele), [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv) and [`NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne`](thm.html#NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset.lean

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
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (hw : w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S) :
    (w.under (𝓞 ↥L)).asIdeal.ramificationIdx' w.asIdeal = 1 := by sorry
