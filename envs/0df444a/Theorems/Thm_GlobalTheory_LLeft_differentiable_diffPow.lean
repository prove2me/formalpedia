-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_differentiable_diffPow
-- name    : GlobalTheory.LLeft.differentiable_diffPow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:48.599227+00:00
-- url     : https://prove2.me/theorems/7423561d-3454-4380-a8a9-62a5497aa99d
-- title:
--   LLeft: differentiable diff Pow
-- statement:
--   The LLeft construction uses the differentiable diff Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L71-L81

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

theorem GlobalTheory.LLeft.differentiable_diffPow (k : ℕ) : ∀ x : ℝ, 0 < x →
    Differentiable ℂ (fun s => diffPow k s x) := by sorry
