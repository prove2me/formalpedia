-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valBall_mem_nhds
-- name    : GroundTheory.LocalField.valBall_mem_nhds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:56.666087+00:00
-- url     : https://prove2.me/theorems/38758b5b-b750-451a-bf20-b1f124a778df
-- title:
--   Local Field: val Ball mem nhds
-- statement:
--   The Local Field construction uses the val Ball mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L66-L67

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

theorem GroundTheory.LocalField.valBall_mem_nhds (n : ℤ) : (valBall K n : Set K) ∈ 𝓝 (0 : K) := by sorry
