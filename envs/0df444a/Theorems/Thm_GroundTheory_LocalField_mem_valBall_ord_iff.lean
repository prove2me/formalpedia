-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_valBall_ord_iff
-- name    : GroundTheory.LocalField.mem_valBall_ord_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:21:16.310093+00:00
-- url     : https://prove2.me/theorems/9f16d0a5-da91-5c59-b732-3c2b8d819cb4
-- title:
--   Local Field: mem val Ball ord iff
-- statement:
--   The Local Field construction uses the mem val Ball ord iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L18-L23

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
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem GroundTheory.LocalField.mem_valBall_ord_iff {c : L} (hc : c ≠ 0) {x : L} :
    x ∈ valBall L (ord c) ↔ ∃ y : 𝒪[L], x = c * y := by sorry
