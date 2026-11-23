-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- name    : GroundTheory.LocalField.valBall_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:39.691166+00:00
-- url     : https://prove2.me/theorems/f3dffa84-b9b1-4b9b-ac02-d91ea23af714
-- title:
--   Local Field: val Ball antitone
-- statement:
--   The Local Field construction uses the val Ball antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L33-L34

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

theorem GroundTheory.LocalField.valBall_antitone {m n : ℤ} (h : m ≤ n) : valBall K n ≤ valBall K m := by sorry
