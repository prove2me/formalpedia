-- Prove2me | Theorems.Thm_Nat_exists_eq_mul_add_of_lt_mul
-- name    : Nat.exists_eq_mul_add_of_lt_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:52.092231+00:00
-- url     : https://prove2.me/theorems/91dceffb-a7bb-4a63-85e6-4119a8b69867
-- title:
--   Nat: exists eq mul add of lt mul
-- statement:
--   Every index below `m * n` is the index of a pair.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L65-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L65-L66

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.exists_eq_mul_add_of_lt_mul {t m n : ℕ} (h : t < m * n) : ∃ a < m, ∃ b < n, t = a * n + b := by sorry
