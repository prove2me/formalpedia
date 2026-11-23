-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_lt
-- name    : GroundTheory.LocalField.isOpen_setOf_valuation_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:49.744807+00:00
-- url     : https://prove2.me/theorems/29ee213a-0688-4d28-913f-c24ae88cc733
-- title:
--   Local Field: is Open set Of valuation lt
-- statement:
--   The Local Field construction uses the is Open set Of valuation lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L60-L70

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.isOpen_setOf_valuation_lt {γ : ValueGroupWithZero K} :
    IsOpen {y : K | valuation K y < γ} := by sorry
