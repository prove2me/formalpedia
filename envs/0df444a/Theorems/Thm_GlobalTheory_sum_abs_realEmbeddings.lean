-- Prove2me | Theorems.Thm_GlobalTheory_sum_abs_realEmbeddings
-- name    : GlobalTheory.sum_abs_realEmbeddings
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:34.181937+00:00
-- url     : https://prove2.me/theorems/27dce0ab-0a7d-403c-b679-1851d4450099
-- title:
--   Global Theory: sum abs real Embeddings
-- statement:
--   The Global Theory construction uses the sum abs real Embeddings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L211-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L211-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.sum_abs_realEmbeddings (x : F) :
    ∑ σ : F →+* ℝ, |σ x| = ∑ σ : F →+* ℂ, ‖σ x‖ := by sorry
