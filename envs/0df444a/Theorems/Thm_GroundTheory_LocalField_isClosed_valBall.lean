-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isClosed_valBall
-- name    : GroundTheory.LocalField.isClosed_valBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:01.394354+00:00
-- url     : https://prove2.me/theorems/73ddb3a2-2e81-4a89-b06b-d00f6d9bbb4f
-- title:
--   Local Field: is Closed val Ball
-- statement:
--   The Local Field construction uses the is Closed val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L63-L64

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

theorem GroundTheory.LocalField.isClosed_valBall (n : ℤ) : IsClosed (valBall K n : Set K) := by sorry
