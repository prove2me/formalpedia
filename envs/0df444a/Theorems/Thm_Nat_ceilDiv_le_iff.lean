-- Prove2me | Theorems.Thm_Nat_ceilDiv_le_iff
-- name    : Nat.ceilDiv_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:21.711189+00:00
-- url     : https://prove2.me/theorems/f8c908b7-aa41-469b-bec7-bdcfb8819650
-- title:
--   Nat: ceil Div le iff
-- statement:
--   `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
--   `b * k` on the right.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L33-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L33-L34

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by sorry
