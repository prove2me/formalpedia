-- Prove2me | Theorems.Thm_Light_polyBound_mono
-- name    : Light.polyBound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:40.353787+00:00
-- url     : https://prove2.me/theorems/0ba0e132-8081-4c5e-a2ed-27dfa5856831
-- title:
--   Light: poly Bound mono
-- statement:
--   The bound grows with its two exponents.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L82-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L82-L85

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

theorem Light.polyBound_mono {s s' k k' : ℕ} (hs : s ≤ s') (hk : k ≤ k') (params : List ℕ) :
    polyBound s k params ≤ polyBound s' k' params := by sorry
