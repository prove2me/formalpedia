-- Prove2me | Theorems.Thm_GroundTheory_LocalField_evalQpow_C_mul_T
-- name    : GroundTheory.LocalField.evalQpow_C_mul_T
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:24.11589+00:00
-- url     : https://prove2.me/theorems/984a4d27-5561-4c7d-9d36-80f41df89a23
-- title:
--   Local Field: eval Qpow C mul T
-- statement:
--   The Local Field construction uses the eval Qpow C mul T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L24-L28

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

theorem GroundTheory.LocalField.evalQpow_C_mul_T (a : ℂ) (n : ℤ) (s : ℂ) :
    evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) s =
      a * ((residueCard K : ℂ) ^ (-s)) ^ n := by sorry
