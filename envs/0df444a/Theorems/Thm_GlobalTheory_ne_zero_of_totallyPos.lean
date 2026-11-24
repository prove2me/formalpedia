-- Prove2me | Theorems.Thm_GlobalTheory_ne_zero_of_totallyPos
-- name    : GlobalTheory.ne_zero_of_totallyPos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:26.189211+00:00
-- url     : https://prove2.me/theorems/b2249a5e-3199-473e-914b-2ec8be316259
-- title:
--   Global Theory: ne zero of totally Pos
-- statement:
--   The Global Theory construction uses the ne zero of totally Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L222-L224

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

theorem GlobalTheory.ne_zero_of_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : a ≠ 0 := by sorry
