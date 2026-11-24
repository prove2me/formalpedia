-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_summable_diffPow
-- name    : GlobalTheory.LLeft.summable_diffPow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:41.02006+00:00
-- url     : https://prove2.me/theorems/7c89c115-ca4f-4215-b86c-348b105572da
-- title:
--   LLeft: summable diff Pow
-- statement:
--   The LLeft construction uses the summable diff Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L149-L156

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

theorem GlobalTheory.LLeft.summable_diffPow (k : ℕ) (s : ℂ) (hs : 1 < s.re + k) :
    Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖) := by sorry
