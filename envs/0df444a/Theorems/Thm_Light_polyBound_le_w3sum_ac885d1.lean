-- Prove2me | Theorems.Thm_Light_polyBound_le_w3sum_ac885d1
-- name    : Light.polyBound_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:40:57.642185+00:00
-- url     : https://prove2.me/theorems/c8c7e2da-be97-4f03-a07e-ff89c8393f08
-- title:
--   Light: poly Bound le
-- statement:
--   At an admissible word size, words have room for a polynomial bound in the parameters, if the
--   slope is large enough.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L56-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L56-L68

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

theorem Light.polyBound_le_w3sum_ac885d1 {b W s k r : ℕ} {params : List ℕ} (h : Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : polyBound s k params ≤ 2 ^ W := by sorry
