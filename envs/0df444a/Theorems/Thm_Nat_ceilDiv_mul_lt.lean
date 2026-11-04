-- Prove2me | Theorems.Thm_Nat_ceilDiv_mul_lt
-- name    : Nat.ceilDiv_mul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:47.822494+00:00
-- url     : https://prove2.me/theorems/48f4560e-8cae-4003-b640-58e75469bdf8
-- title:
--   Nat: ceil Div mul lt
-- statement:
--   `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L45-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L45-L48

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by sorry
