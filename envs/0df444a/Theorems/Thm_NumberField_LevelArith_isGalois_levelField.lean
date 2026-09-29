-- Prove2me | Theorems.Thm_NumberField_LevelArith_isGalois_levelField
-- name    : NumberField.LevelArith.isGalois_levelField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/75c4cae5-3757-5cda-8fa7-bcf85c3799ac
-- title:
--   The layer F_L/L is Galois for F/ℚ finite normal
-- statement:
--   Let $L$ and $F$ be intermediate fields of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (the algebraic closure `AlgebraicClosure ℚ`), with $L \le F$, and assume that $F$ is finite-dimensional over $\mathbb{Q}$ and normal over $\mathbb{Q}$. Then the field $F$, viewed through `levelField L F hLF` as an intermediate field of $L \subseteq \overline{\mathbb{Q}}$ — that is, the same subfield of $\overline{\mathbb{Q}}$ with its $L$-algebra structure, obtained by extension of scalars along $L \le F$ — is Galois over $L$. Thus the assertion is that $F/L$ is normal and separable, for every intermediate $L$ below a field $F$ that is finite and normal over $\mathbb{Q}$; no hypothesis is placed on $L$ itself beyond $L \le F$, and the ambient characteristic zero supplies separability.
--
--   This is the standard statement that normality (hence, in characteristic zero, the Galois property) passes to the top layer of a tower: if $F/\mathbb{Q}$ is finite and normal then $F/L$ is Galois for any intermediate $L$. It provides the Galois instance for the layer $F_L/L$ used by the level-arithmetic statements about unramifiedness outside a finite set and divisibility of the cardinalities of decomposition groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_isGalois_levelField.lean

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

theorem NumberField.LevelArith.isGalois_levelField
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] :
    IsGalois ↥L ↥(levelField L F hLF) := by sorry
