-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isOpen_range_pow
-- name    : GroundTheory.LocalField.isOpen_range_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:03.948673+00:00
-- url     : https://prove2.me/theorems/d1a79b4f-04ae-4683-86d4-191617dffc31
-- title:
--   Local Field: is Open range pow
-- statement:
--   The Local Field construction uses the is Open range pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L194-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L194-L200

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

theorem GroundTheory.LocalField.isOpen_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by sorry
