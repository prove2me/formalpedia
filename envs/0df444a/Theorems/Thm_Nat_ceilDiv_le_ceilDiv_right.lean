-- Prove2me | Theorems.Thm_Nat_ceilDiv_le_ceilDiv_right
-- name    : Nat.ceilDiv_le_ceilDiv_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:50.281555+00:00
-- url     : https://prove2.me/theorems/f1120451-4cf3-49f7-845f-1a100fca5c85
-- title:
--   Nat: ceil Div le ceil Div right
-- statement:
--   More to cover needs at least as many pieces.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L51-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L51-L52

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.ceilDiv_le_ceilDiv_right {a a' : ℕ} (h : a ≤ a') (b : ℕ) : a ⌈/⌉ b ≤ a' ⌈/⌉ b := by sorry
