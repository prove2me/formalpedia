-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_valBall_one_iff
-- name    : GroundTheory.LocalField.mem_valBall_one_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:33.234046+00:00
-- url     : https://prove2.me/theorems/f022007c-0310-4a19-b60c-fe9f8b5fb30b
-- title:
--   Local Field: mem val Ball one iff
-- statement:
--   The Local Field construction uses the mem val Ball one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L43-L48

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.mem_valBall_one_iff {x : K} : x ∈ valBall K 1 ↔ valuation K x < 1 := by sorry
