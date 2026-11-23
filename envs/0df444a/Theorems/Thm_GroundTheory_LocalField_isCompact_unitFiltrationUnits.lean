-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isCompact_unitFiltrationUnits
-- name    : GroundTheory.LocalField.isCompact_unitFiltrationUnits
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:31.453872+00:00
-- url     : https://prove2.me/theorems/853563dc-0553-45a6-8750-ba245b2cffd7
-- title:
--   Local Field: is Compact unit Filtration Units
-- statement:
--   The Local Field construction uses the is Compact unit Filtration Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L127-L146

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

theorem GroundTheory.LocalField.isCompact_unitFiltrationUnits (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by sorry
