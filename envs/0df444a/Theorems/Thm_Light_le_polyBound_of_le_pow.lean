-- Prove2me | Theorems.Thm_Light_le_polyBound_of_le_pow
-- name    : Light.le_polyBound_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:03.870914+00:00
-- url     : https://prove2.me/theorems/312dc399-a4db-4de6-9413-daa1f9f6c2e0
-- title:
--   Light: le poly Bound of le pow
-- statement:
--   A number that is at most A (n + 1)^e with e ≤ k has a bound of this form in n.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L88-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L88-L96

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

theorem Light.le_polyBound_of_le_pow {n A s m e k : ℕ} (he : e ≤ k) (h : m ≤ A * (n + 1) ^ e) :
    m ≤ polyBound (s + Nat.size A) k [n] := by sorry
