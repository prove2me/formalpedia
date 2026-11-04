-- Prove2me | Theorems.Thm_Nat_succ_div_mod_of_ne
-- name    : Nat.succ_div_mod_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:54.820212+00:00
-- url     : https://prove2.me/theorems/5eaa0a92-7c37-4820-a65e-4a4fa4c19816
-- title:
--   Nat: succ div mod of ne
-- statement:
--   The next index, if the test "is this the end of the row?" fails.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L86-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L86-L88

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.succ_div_mod_of_ne {n i : ℕ} (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by sorry
