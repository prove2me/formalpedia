-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coe_normUnits
-- name    : GroundTheory.LocalField.coe_normUnits
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:20.015375+00:00
-- url     : https://prove2.me/theorems/cd139c01-a4eb-4e7f-bac6-a8728f77b03d
-- title:
--   Local Field: coe norm Units
-- statement:
--   The Local Field construction uses the coe norm Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L25-L26

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
variable {K L}

theorem GroundTheory.LocalField.coe_normUnits (x : Lˣ) : ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) := by sorry

attribute [defeq] GroundTheory.LocalField.coe_normUnits
