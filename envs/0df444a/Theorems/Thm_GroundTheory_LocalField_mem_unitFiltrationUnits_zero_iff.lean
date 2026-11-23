-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_zero_iff
-- name    : GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:02.286819+00:00
-- url     : https://prove2.me/theorems/593034de-e541-45fc-83de-164f229d6565
-- title:
--   Local Field: mem unit Filtration Units zero iff
-- statement:
--   The Local Field construction uses the mem unit Filtration Units zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L20-L23

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

theorem GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by sorry
