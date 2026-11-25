-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_norm_taylor_two_le
-- name    : GroundTheory.Global.Quadratic.norm_taylor_two_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:15.275804+00:00
-- url     : https://prove2.me/theorems/80ec2c68-065b-4ea3-a8b9-9b1a0abb0a0a
-- title:
--   Quadratic: norm taylor two le
-- statement:
--   The Quadratic construction uses the norm taylor two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L24-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L24-L67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic

theorem GroundTheory.Global.Quadratic.norm_taylor_two_le (n : ℕ) (s : ℂ) {a b M : ℝ}
    (hpos : ∀ t ∈ uIcc a b, 0 < (n : ℝ) + t)
    (hM : ∀ t ∈ uIcc a b, ‖s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2)‖ ≤ M) :
    ‖(((n : ℝ) + b : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + a : ℝ) : ℂ) ^ (-s - 1)) * ((b - a : ℝ) : ℂ)‖ ≤ M * |b - a| ^ 2 := by sorry
