-- Prove2me | Theorems.Thm_NumberField_LevelArith_eq_one_of_mem_infPlaceDecomp_of_isPGroup
-- name    : NumberField.LevelArith.eq_one_of_mem_infPlaceDecomp_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/02185258-6128-5458-a1f6-e2caf8c079f9
-- title:
--   Trivial decomposition at infinity in a p-group layer
-- statement:
--   Let $p$ be a prime and let $L$ be an intermediate field of $\mathbb{Q}\subseteq\overline{\mathbb{Q}}$ that is finite over $\mathbb{Q}$, subject to the condition that if $p=2$ then $L$ contains an element $i$ with $i^{2}=-1$. Let $F$ be a further intermediate field with $L\le F$, finite over $\mathbb{Q}$ and normal over $\mathbb{Q}$, and write $\mathrm{levelField}\,L\,F$ for $F$ regarded, via `IntermediateField.extendScalars`, as an intermediate field of $\overline{\mathbb{Q}}$ over $L$; assume this extension of $L$ is Galois. Assume further that the quotient of the fixing subgroup of $L$ in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ by the preimage in it of the fixing subgroup of $F$ — that is, $\mathrm{Gal}(\overline{\mathbb{Q}}/L)/\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ — is a $p$-group. Then for every infinite place $v$ of $\mathrm{levelField}\,L\,F$ and every $L$-algebra automorphism $g$ of $\mathrm{levelField}\,L\,F$ lying in the decomposition group at $v$, defined as the stabiliser of $v$ for the action of the automorphism group on infinite places, one has $g=1$. In other words the decomposition group of every archimedean place of $F$ over $L$ is trivial.
--
--   This is the standard fact that in a $p$-extension the archimedean places are undecomposed: decomposition groups at infinity have order at most $2$, hence are trivial when $p$ is odd, and for $p=2$ the presence of $\sqrt{-1}$ in the base makes every place complex. It is used to supply the triviality-at-infinity hypothesis in the vanishing results for the $S$-idèle cohomology in degrees two and three.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_eq_one_of_mem_infPlaceDecomp_of_isPGroup.lean

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

theorem NumberField.LevelArith.eq_one_of_mem_infPlaceDecomp_of_isPGroup
    {p : ℕ} [Fact p.Prime] (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (v : InfinitePlace ↥(levelField L F hLF)) (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (hg : g ∈ NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) v) : g = 1 := by sorry
