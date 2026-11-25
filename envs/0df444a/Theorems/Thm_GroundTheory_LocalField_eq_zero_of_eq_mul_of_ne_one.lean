-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_eq_mul_of_ne_one
-- name    : GroundTheory.LocalField.eq_zero_of_eq_mul_of_ne_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:24.576519+00:00
-- url     : https://prove2.me/theorems/3f468e88-a6cb-59e7-b22d-8ad5d51aba71
-- title:
--   Local Field: eq zero of eq mul of ne one
-- statement:
--   The Local Field construction uses the eq zero of eq mul of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L84-L86

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.eq_zero_of_eq_mul_of_ne_one {a c : ℂ} (ha : a ≠ 1) (h : c = a * c) : c = 0 := by sorry
