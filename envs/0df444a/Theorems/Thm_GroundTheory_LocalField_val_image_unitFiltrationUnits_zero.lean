-- Prove2me | Theorems.Thm_GroundTheory_LocalField_val_image_unitFiltrationUnits_zero
-- name    : GroundTheory.LocalField.val_image_unitFiltrationUnits_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:36.061648+00:00
-- url     : https://prove2.me/theorems/734edf54-6167-446e-8f2a-cd257ada6260
-- title:
--   Local Field: val image unit Filtration Units zero
-- statement:
--   The Local Field construction uses the val image unit Filtration Units zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L81-L89

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

theorem GroundTheory.LocalField.val_image_unitFiltrationUnits_zero :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by sorry
