-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_embedding_eq_zero
-- name    : GlobalTheory.eq_zero_of_embedding_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:30.43517+00:00
-- url     : https://prove2.me/theorems/b1bba157-4640-4a7b-956d-d16e1550212a
-- title:
--   Global Theory: eq zero of embedding eq zero
-- statement:
--   The Global Theory construction uses the eq zero of embedding eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FinrankMulDiscrRpowLeSumSqOfMemTraceDual.lean#L151-L153

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
omit [NumberField K]

theorem GlobalTheory.eq_zero_of_embedding_eq_zero {A : Type*} [Ring A] [Nontrivial A] (σ : K →+* A) {x : K}
    (h : σ x = 0) : x = 0 := by sorry
