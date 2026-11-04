-- Prove2me | Theorems.Thm_Nat_mod_lt_of_lt_mul
-- name    : Nat.mod_lt_of_lt_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:51.77302+00:00
-- url     : https://prove2.me/theorems/fdbcafa7-6351-460b-b9d4-75547c8d408d
-- title:
--   Nat: mod lt of lt mul
-- statement:
--   The column of an index below `m * n` is below `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L61-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L61-L62

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.mod_lt_of_lt_mul {t m n : ℕ} (h : t < m * n) : t % n < n := by sorry
