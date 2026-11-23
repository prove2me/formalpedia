-- Prove2me | Theorems.Thm_GroundTheory_LocalField_one_le_absRamificationIndex
-- name    : GroundTheory.LocalField.one_le_absRamificationIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:03.855675+00:00
-- url     : https://prove2.me/theorems/3ea17aff-9e67-42a8-b7f3-acc7224fadcc
-- title:
--   Local Field: one le abs Ramification Index
-- statement:
--   The Local Field construction uses the one le abs Ramification Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L161-L167

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
include p

theorem GroundTheory.LocalField.one_le_absRamificationIndex : 1 ≤ absRamificationIndex K := by sorry
