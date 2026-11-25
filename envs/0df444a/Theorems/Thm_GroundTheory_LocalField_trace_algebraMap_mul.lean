-- Prove2me | Theorems.Thm_GroundTheory_LocalField_trace_algebraMap_mul
-- name    : GroundTheory.LocalField.trace_algebraMap_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:43.457087+00:00
-- url     : https://prove2.me/theorems/f65aa821-c630-5164-9e0a-37821b7b84e9
-- title:
--   Local Field: trace algebra Map mul
-- statement:
--   The Local Field construction uses the trace algebra Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
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
open ValuativeRel
open scoped nonZeroDivisors
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem GroundTheory.LocalField.trace_algebraMap_mul (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by sorry
