-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_range_pow_le
-- name    : GroundTheory.LocalField.exists_range_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:08.780803+00:00
-- url     : https://prove2.me/theorems/93d9b1ae-168c-4285-bb96-641a0c81c61a
-- title:
--   Local Field: exists range pow le
-- statement:
--   The Local Field construction uses the exists range pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean#L183-L187

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

theorem GroundTheory.LocalField.exists_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by sorry
