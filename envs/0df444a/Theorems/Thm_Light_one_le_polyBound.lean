-- Prove2me | Theorems.Thm_Light_one_le_polyBound
-- name    : Light.one_le_polyBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:40:59.566778+00:00
-- url     : https://prove2.me/theorems/d062a0ba-92a9-4f0b-9eaa-f1f371699471
-- title:
--   Light: one le poly Bound
-- statement:
--   The bound is positive.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L71-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L71-L73

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
set_option autoImplicit false
section
open Light
open ThreeSumApsp.WordRam

theorem Light.one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by sorry
