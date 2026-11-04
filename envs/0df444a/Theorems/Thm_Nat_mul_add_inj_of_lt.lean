-- Prove2me | Theorems.Thm_Nat_mul_add_inj_of_lt
-- name    : Nat.mul_add_inj_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:48.026661+00:00
-- url     : https://prove2.me/theorems/9beec9f1-e180-42b6-9e9a-cc4a17149152
-- title:
--   Nat: mul add inj of lt
-- statement:
--   The index determines the pair.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L50-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L50-L54

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.mul_add_inj_of_lt {a b a' b' n : ℕ} (hb : b < n) (hb' : b' < n)
    (h : a * n + b = a' * n + b') :
    a = a' ∧ b = b' := by sorry
