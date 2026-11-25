-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_or_totallyPos
-- name    : GlobalTheory.eq_zero_or_totallyPos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:06.559869+00:00
-- url     : https://prove2.me/theorems/2dfb336a-5d2e-4d53-a381-f97edfea940f
-- title:
--   Global Theory: eq zero or totally Pos
-- statement:
--   The Global Theory construction uses the eq zero or totally Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L247-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L247-L251

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

theorem GlobalTheory.eq_zero_or_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 ≤ σ a) :
    a = 0 ∨ ∀ σ : F →+* ℝ, 0 < σ a := by sorry
