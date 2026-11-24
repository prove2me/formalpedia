-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_hasDerivAt_diffPow
-- name    : GlobalTheory.LLeft.hasDerivAt_diffPow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:49.200747+00:00
-- url     : https://prove2.me/theorems/d8a4ef77-c33f-46f5-9487-0d20505ad6dd
-- title:
--   LLeft: has Deriv At diff Pow
-- statement:
--   The LLeft construction uses the has Deriv At diff Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L11-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft

theorem GlobalTheory.LLeft.hasDerivAt_diffPow (k : ℕ) (s : ℂ) : ∀ x : ℝ, 0 < x →
    HasDerivAt (diffPow k s) (-s * diffPow k (s + 1) x) x := by sorry
