-- Prove2me | Theorems.Thm_Nat_mul_add_lt_mul
-- name    : Nat.mul_add_lt_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:45.953917+00:00
-- url     : https://prove2.me/theorems/9afce93d-ace8-4ef7-92ff-75d4f003c924
-- title:
--   Nat: mul add lt mul
-- statement:
--   The index of an entry of a matrix with `m` rows and `n` columns is below `m * n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L32-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L32-L33

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.mul_add_lt_mul {a b m n : ℕ} (ha : a < m) (hb : b < n) : a * n + b < m * n := by sorry
