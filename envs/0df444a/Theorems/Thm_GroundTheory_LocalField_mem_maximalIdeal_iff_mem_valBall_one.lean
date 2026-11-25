-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_iff_mem_valBall_one
-- name    : GroundTheory.LocalField.mem_maximalIdeal_iff_mem_valBall_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:49.446375+00:00
-- url     : https://prove2.me/theorems/c44d5bad-6555-4256-8fd3-9e2f1fb1a239
-- title:
--   Local Field: mem maximal Ideal iff mem val Ball one
-- statement:
--   The Local Field construction uses the mem maximal Ideal iff mem val Ball one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L50-L52

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

theorem GroundTheory.LocalField.mem_maximalIdeal_iff_mem_valBall_one {z : 𝒪[K]} : z ∈ 𝓂[K] ↔ (z : K) ∈ valBall K 1 := by sorry
