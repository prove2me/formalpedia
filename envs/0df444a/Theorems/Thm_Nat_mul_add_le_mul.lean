-- Prove2me | Theorems.Thm_Nat_mul_add_le_mul
-- name    : Nat.mul_add_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:46.73027+00:00
-- url     : https://prove2.me/theorems/917864c1-9a14-4f09-ad62-956dfda600a3
-- title:
--   Nat: mul add le mul
-- statement:
--   Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L36-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L36-L39

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n := by sorry
