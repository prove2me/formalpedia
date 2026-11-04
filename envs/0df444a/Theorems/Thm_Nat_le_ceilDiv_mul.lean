-- Prove2me | Theorems.Thm_Nat_le_ceilDiv_mul
-- name    : Nat.le_ceilDiv_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:31.813434+00:00
-- url     : https://prove2.me/theorems/5d16b8f5-553d-444b-8653-fe9365f6489d
-- title:
--   Nat: le ceil Div mul
-- statement:
--   `a ⌈/⌉ b` pieces of size `b` cover `a`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L41-L42

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ a ⌈/⌉ b * b := by sorry
