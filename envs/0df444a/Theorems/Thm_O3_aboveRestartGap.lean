-- Prove2me | Theorems.Thm_O3_aboveRestartGap
-- name    : O3.aboveRestartGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:16.803134+00:00
-- url     : https://prove2.me/theorems/745a955a-0763-46b2-92c2-2061326281a2
-- title:
--   O3: above Restart Gap
-- statement:
--   The restart induction: halving a proved gap at each successful level gives
--   `gap_s <= Delta_s`.  This is purely the scalar induction after the missing
--   uniform-convexity and phase-rate steps have produced the halving premise.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L230-L240
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L230-L240

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveRestartGap
    {Delta0 : ℝ} (gap : ℕ → ℝ)
    (hzero : gap 0 ≤ Delta0)
    (hstep : ∀ s, gap (s + 1) ≤ gap s / 2) :
    ∀ s, gap s ≤ aboveLevel Delta0 s := by sorry
