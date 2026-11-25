-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algebraMap_norm_eq_prod
-- name    : GroundTheory.LocalField.algebraMap_norm_eq_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:15:19.650971+00:00
-- url     : https://prove2.me/theorems/e4ffe1ff-0aa0-4af0-be0b-7a6021ee93ed
-- title:
--   Local Field: algebra Map norm eq prod
-- statement:
--   The Local Field construction uses the algebra Map norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

theorem GroundTheory.LocalField.algebraMap_norm_eq_prod [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : L ≃ₐ[K] L, σ x := by sorry
