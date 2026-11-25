-- Prove2me | Theorems.Thm_GroundTheory_LocalField_forall_trace_mul_mem_iff
-- name    : GroundTheory.LocalField.forall_trace_mul_mem_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:37.656802+00:00
-- url     : https://prove2.me/theorems/9e8ba377-f57c-5635-b348-640c5ce9b21d
-- title:
--   Local Field: forall trace mul mem iff
-- statement:
--   The Local Field construction uses the forall trace mul mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L28-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L28-L61

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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.forall_trace_mul_mem_iff (x : L) :
    (∀ z : 𝒪[L], Algebra.trace K L (x * z) ∈ 𝒪[K]) ↔
      x ∈ valBall L (-(differentExponent K L : ℤ)) := by sorry
