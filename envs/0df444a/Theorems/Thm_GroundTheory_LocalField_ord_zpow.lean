-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_zpow
-- name    : GroundTheory.LocalField.ord_zpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:27.68813+00:00
-- url     : https://prove2.me/theorems/9eb1ab9e-e6ab-4b08-a70b-1c5bcbe8c0b8
-- title:
--   Local Field: ord zpow
-- statement:
--   The Local Field construction uses the ord zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L38-L42

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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.ord_zpow {x : K} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by sorry
