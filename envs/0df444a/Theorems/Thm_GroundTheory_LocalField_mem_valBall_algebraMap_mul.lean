-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_valBall_algebraMap_mul
-- name    : GroundTheory.LocalField.mem_valBall_algebraMap_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:23:13.192677+00:00
-- url     : https://prove2.me/theorems/287e2ca4-368d-45fb-8b89-571be13bc811
-- title:
--   Local Field: mem val Ball algebra Map mul
-- statement:
--   The Local Field construction uses the mem val Ball algebra Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L84-L87

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
variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

theorem GroundTheory.LocalField.mem_valBall_algebraMap_mul {m : ℤ} {x : L} (hx : x ∈ valBall L m) {a : K}
    (ha : a ∈ 𝒪[K]) : algebraMap K L a * x ∈ valBall L m := by sorry
