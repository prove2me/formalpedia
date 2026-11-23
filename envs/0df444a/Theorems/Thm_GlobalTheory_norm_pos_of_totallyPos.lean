-- Prove2me | Theorems.Thm_GlobalTheory_norm_pos_of_totallyPos
-- name    : GlobalTheory.norm_pos_of_totallyPos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:25.381236+00:00
-- url     : https://prove2.me/theorems/0986fd47-aaee-431f-8eea-df01e2c443f6
-- title:
--   Global Theory: norm pos of totally Pos
-- statement:
--   The Global Theory construction uses the norm pos of totally Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L216-L220

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

theorem GlobalTheory.norm_pos_of_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : 0 < Algebra.norm ℚ a := by sorry
