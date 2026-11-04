-- Prove2me | Theorems.Thm_Nat_ceil_div_eq_ceilDiv
-- name    : Nat.ceil_div_eq_ceilDiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:52.695969+00:00
-- url     : https://prove2.me/theorems/26903a35-ffc3-407b-bee0-ee3ebb761e31
-- title:
--   Nat: ceil div eq ceil Div
-- statement:
--   The ceiling of the real quotient of two natural numbers, in natural numbers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L55-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Ceil.lean#L55-L58

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
set_option autoImplicit false
section
open Nat

theorem Nat.ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by sorry
