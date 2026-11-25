-- Prove2me | Theorems.Thm_GroundTheory_LocalField_evalQpow_mul
-- name    : GroundTheory.LocalField.evalQpow_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:46.136267+00:00
-- url     : https://prove2.me/theorems/be723c6f-dfda-54af-adcf-7534aeed8df8
-- title:
--   Local Field: eval Qpow mul
-- statement:
--   The Local Field construction uses the eval Qpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L33-L34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
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

theorem GroundTheory.LocalField.evalQpow_mul (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P * Q) s = evalQpow K P s * evalQpow K Q s := by sorry
