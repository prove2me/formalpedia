-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_le_le_isPGroup_quotient_not_dvd_finrank
-- name    : NumberField.LevelArith.exists_le_le_isPGroup_quotient_not_dvd_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d078f186-9b1f-5a2a-9f08-5b6849809c5c
-- title:
--   Existence of a Sylow intermediate field for a finite layer
-- statement:
--   Let $p$ be a prime and let $L \subseteq F$ be intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$ (realised as `IntermediateField ℚ (AlgebraicClosure ℚ)`), both finite over $\mathbb{Q}$, with $F$ normal over $\mathbb{Q}$. The assertion is that there exists an intermediate field $L'$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L \le L' \le F$, finite over $\mathbb{Q}$, such that: the extension $L'F$, i.e. $F$ regarded via `levelField L' F` (scalars extended to $L'$) as an intermediate field of $\overline{\mathbb{Q}}/L'$, is Galois over $L'$; the quotient of the fixing subgroup of $L'$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ by the preimage of the fixing subgroup of $F$ under the inclusion of the fixing subgroup of $L'$ — that is, $\mathrm{Gal}(\overline{\mathbb{Q}}/L')/\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ — is a $p$-group in the sense that each of its elements has order a power of $p$; and $p$ does not divide $\mathrm{finrank}_{L}$ of $F$'s analogue for $L'$, namely the degree of `levelField L L'`, which is $[L' : L]$.
--
--   This is the classical passage to the fixed field of a Sylow $p$-subgroup of $\mathrm{Gal}(F/L)$, the device that reduces assertions about an arbitrary finite Galois layer to the case of a $p$-group layer, since restriction to a layer of degree prime to $p$ is injective on $p$-primary cohomology. It is used in the level-arithmetic results on vanishing of inflated degree-two classes and on finding a level where prescribed cochain identities hold.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_le_le_isPGroup_quotient_not_dvd_finrank.lean

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

theorem NumberField.LevelArith.exists_le_le_isPGroup_quotient_not_dvd_finrank
    (p : ℕ) [Fact p.Prime] (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] :
    ∃ (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (_ : FiniteDimensional ℚ ↥L')
      (_ : IsGalois ↥L' ↥(levelField L' F hL'F)),
      IsPGroup p (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) ∧ ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL') := by sorry
