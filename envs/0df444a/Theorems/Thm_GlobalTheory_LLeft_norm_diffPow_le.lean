-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_norm_diffPow_le
-- name    : GlobalTheory.LLeft.norm_diffPow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:13.305097+00:00
-- url     : https://prove2.me/theorems/4fa6c24f-c3db-4cd8-9034-81d09ecf9c34
-- title:
--   LLeft: norm diff Pow le
-- statement:
--   The LLeft construction uses the norm diff Pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L37-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L37-L69

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

theorem GlobalTheory.LLeft.norm_diffPow_le (k : ℕ) : ∀ (s : ℂ) (x : ℝ), 0 < x → 0 ≤ s.re + k →
    ‖diffPow k s x‖ ≤ (‖s‖ + k) ^ k * x ^ (-(s.re + k)) := by sorry
