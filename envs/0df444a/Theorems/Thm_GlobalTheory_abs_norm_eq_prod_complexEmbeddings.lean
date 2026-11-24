-- Prove2me | Theorems.Thm_GlobalTheory_abs_norm_eq_prod_complexEmbeddings
-- name    : GlobalTheory.abs_norm_eq_prod_complexEmbeddings
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:19.16504+00:00
-- url     : https://prove2.me/theorems/dded3026-1c41-448d-8d8b-bffe4bd1da55
-- title:
--   Global Theory: abs norm eq prod complex Embeddings
-- statement:
--   The Global Theory construction uses the abs norm eq prod complex Embeddings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L35-L37

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
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by sorry
