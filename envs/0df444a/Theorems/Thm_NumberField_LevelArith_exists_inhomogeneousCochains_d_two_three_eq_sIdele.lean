-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele
-- name    : NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d3db87f8-b60c-56e6-bc6b-0636ced1c03f
-- title:
--   Vanishing of H³ of the S-idèle module of a level
-- statement:
--   Fix a finite set $S$ of rational primes and two intermediate fields $L \le F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, both finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$. Assume each of $L$ and $F$ is unramified outside $S$ in the sense of `IsUnramifiedOutside`: it is finite over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field. Write $F_L =$ `levelField L F hLF` for $F$ regarded as an intermediate field of $\overline{\mathbb{Q}}/L$, assumed Galois over $L$, and assume further that for every infinite place $v$ of $F_L$ the decomposition subgroup of $v$, i.e. its stabiliser in $\mathrm{Gal}(F_L/L)$, is trivial. Let $J$ be the $S$-idèle representation [`NumberField.SIdele.obj`](def/NumberField_SIdeleModule.html#L75) of $\mathrm{Gal}(F_L/L)$ over $\mathbb{Z}$ attached to the finset of primes of $\mathcal{O}_L$ lying over $S$: the product over that index of the modules coinduced from the decomposition subgroups, local units at the primes in the finset, local integral units at the primes outside it, and local units at the places above each infinite place of $L$. Then every $u \colon (\mathrm{Fin}\,3 \to \mathrm{Gal}(F_L/L)) \to J$ killed by the differential $d^{3,4}$ of the inhomogeneous cochain complex of $J$ is of the form $d^{2,3} c$ for some $c \colon (\mathrm{Fin}\,2 \to \mathrm{Gal}(F_L/L)) \to J$.
--
--   This is the cochain-level form of the vanishing $H^3(\mathrm{Gal}(F_L/L), J) = 0$ for the $S$-idèle module of a level $F_L$ whose infinite places are undecomposed over $L$. It feeds the descent steps [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_isPGroup) and [`NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup`](thm.html#NumberField.LevelArith.exists_level_inhomogeneousCochains_d_two_three_eq_of_pow_smul_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hinf : ∀ (v : InfinitePlace ↥(levelField L F hLF)) (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))), g ∈ NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) v → g = 1)
    (u : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hu : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = u := by sorry
