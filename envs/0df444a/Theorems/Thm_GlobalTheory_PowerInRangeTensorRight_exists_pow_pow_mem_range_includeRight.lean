-- Prove2me | Theorems.Thm_GlobalTheory_PowerInRangeTensorRight_exists_pow_pow_mem_range_includeRight
-- name    : GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:10.026256+00:00
-- url     : https://prove2.me/theorems/e411154d-9018-4e74-b990-4592c4eff443
-- title:
--   Power In Range Tensor Right: exists pow pow mem range include Right
-- statement:
--   The Power In Range Tensor Right construction uses the exists pow pow mem range include Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowPowMemRangeIncludeRight.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowPowMemRangeIncludeRight.lean#L7-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowPowMemRangeIncludeRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerInRangeTensorRight
open TensorProduct

theorem GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by sorry
