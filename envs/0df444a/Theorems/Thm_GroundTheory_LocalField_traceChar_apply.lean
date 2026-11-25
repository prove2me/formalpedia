-- Prove2me | Theorems.Thm_GroundTheory_LocalField_traceChar_apply
-- name    : GroundTheory.LocalField.traceChar_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:23:59.086+00:00
-- url     : https://prove2.me/theorems/f6fad87d-c25f-4b54-8b00-b619029c80b1
-- title:
--   Local Field: trace Char apply
-- statement:
--   The Local Field construction uses the trace Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L74-L75

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

theorem GroundTheory.LocalField.traceChar_apply (ψ : AddChar K Circle) (x : L) :
    traceChar L ψ x = ψ (Algebra.trace K L x) := by sorry
