-- Prove2me | Theorems.Thm_Nat_succ_div_mod_of_eq
-- name    : Nat.succ_div_mod_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:55.400135+00:00
-- url     : https://prove2.me/theorems/b8b2cd3a-3ee4-4191-a742-d2c5124983e2
-- title:
--   Nat: succ div mod of eq
-- statement:
--   After the last index of a row comes the first index of the next row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L91-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L91-L99

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by sorry
