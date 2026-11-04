-- Prove2me | Theorems.Thm_Nat_pow_clog_le_mul
-- name    : Nat.pow_clog_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:54.65898+00:00
-- url     : https://prove2.me/theorems/edbbe62b-16b5-4494-8c59-82d2cf3a447a
-- title:
--   Nat: pow clog le mul
-- statement:
--   Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L66-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L66-L73

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by sorry
