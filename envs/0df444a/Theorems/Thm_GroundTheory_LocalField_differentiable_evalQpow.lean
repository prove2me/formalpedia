-- Prove2me | Theorems.Thm_GroundTheory_LocalField_differentiable_evalQpow
-- name    : GroundTheory.LocalField.differentiable_evalQpow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:04.401482+00:00
-- url     : https://prove2.me/theorems/8b1129e9-b6a7-5b4f-9690-2cffbead32be
-- title:
--   Local Field: differentiable eval Qpow
-- statement:
--   The Local Field construction uses the differentiable eval Qpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L51-L63

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

theorem GroundTheory.LocalField.differentiable_evalQpow (P : LaurentPolynomial ℂ) : Differentiable ℂ (evalQpow K P) := by sorry
