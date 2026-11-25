-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indicator_valBall_zero_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.indicator_valBall_zero_mem_schwartzBruhat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:08.097446+00:00
-- url     : https://prove2.me/theorems/8202036f-cb63-5321-a2dd-cc8a1c8fdfff
-- title:
--   Local Field: indicator val Ball zero mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the indicator val Ball zero mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L62-L72

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
omit [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.indicator_valBall_zero_mem_schwartzBruhat :
    (valBall K 0 : Set K).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat K := by sorry
