-- Prove2me | Theorems.Thm_Nat_eq_mul_succ_iff
-- name    : Nat.eq_mul_succ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:52.22122+00:00
-- url     : https://prove2.me/theorems/dd0f219d-f8a0-447c-b8a5-9c0331f10864
-- title:
--   Nat: eq mul succ iff
-- statement:
--   The indices of the diagonal are the multiples of `n + 1`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L69-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L69-L75

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem Nat.eq_mul_succ_iff {n i t : ℕ} (hi : i < n) : t = i * (n + 1) ↔ t / n = i ∧ t % n = i := by sorry
