-- Prove2me | Theorems.Thm_Light_polyBound_cons_le
-- name    : Light.polyBound_cons_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:22.153198+00:00
-- url     : https://prove2.me/theorems/2f408bc1-f31b-476b-8e75-9a78c87c366b
-- title:
--   Light: poly Bound cons le
-- statement:
--   The bound grows with its first parameter.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L76-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L76-L79

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

theorem Light.polyBound_cons_le {p p' : ℕ} (h : p ≤ p') (s k : ℕ) (params : List ℕ) :
    polyBound s k (p :: params) ≤ polyBound s k (p' :: params) := by sorry
