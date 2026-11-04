-- Prove2me | Theorems.Thm_Nat_lt_ceilDiv_iff
-- name    : Nat.lt_ceilDiv_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:31.898187+00:00
-- url     : https://prove2.me/theorems/058869b7-1e49-473e-a532-60848284662b
-- title:
--   Nat: lt ceil Div iff
-- statement:
--   `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L37-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L37-L38

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by sorry
