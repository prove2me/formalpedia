-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits
-- name    : GroundTheory.LocalField.isOpen_unitFiltrationUnits
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:46.46425+00:00
-- url     : https://prove2.me/theorems/daeae3d0-f002-42e9-9c75-e31331a319b1
-- title:
--   Local Field: is Open unit Filtration Units
-- statement:
--   The Local Field construction uses the is Open unit Filtration Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L113-L125

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

theorem GroundTheory.LocalField.isOpen_unitFiltrationUnits (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by sorry
