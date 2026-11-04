-- Prove2me | Theorems.Thm_Light_add_le_polyBound
-- name    : Light.add_le_polyBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:16.729505+00:00
-- url     : https://prove2.me/theorems/8c6595ae-0eff-4067-8013-2e188742c080
-- title:
--   Light: add le poly Bound
-- statement:
--   The sum of two numbers with such bounds has such a bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L115-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L115-L120

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

theorem Light.add_le_polyBound {a b s s' k k' : ℕ} {params : List ℕ} (ha : a ≤ polyBound s k params)
    (hb : b ≤ polyBound s' k' params) : a + b ≤ polyBound (1 + (s + s')) (k + k') params := by sorry
