-- Prove2me | Theorems.Thm_Nat_succ_div_mod_of_lt
-- name    : Nat.succ_div_mod_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:54.837273+00:00
-- url     : https://prove2.me/theorems/629975a7-dd9e-460a-ba48-2d500b403216
-- title:
--   Nat: succ div mod of lt
-- statement:
--   The next index, if it is in the same row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L80-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L80-L83

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by sorry
