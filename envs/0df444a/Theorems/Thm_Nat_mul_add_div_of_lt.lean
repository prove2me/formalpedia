-- Prove2me | Theorems.Thm_Nat_mul_add_div_of_lt
-- name    : Nat.mul_add_div_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:47.400324+00:00
-- url     : https://prove2.me/theorems/77ce3b6a-4a6a-4c8e-acc6-07d08729d06f
-- title:
--   Nat: mul add div of lt
-- statement:
--   The row of the index `a * n + b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L46-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L46-L47

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.mul_add_div_of_lt {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a := by sorry
