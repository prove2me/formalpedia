-- Prove2me | Theorems.Thm_Light_polyBound_pair_le
-- name    : Light.polyBound_pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:14.917169+00:00
-- url     : https://prove2.me/theorems/e0cba526-bae5-4c6b-ac42-affab0483c6b
-- title:
--   Light: poly Bound pair le
-- statement:
--   A bound in two parameters is a bound in n, of twice the degree, if both are at most n.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L99-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/WordSize.lean#L99-L107

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

theorem Light.polyBound_pair_le {s k p₁ p₂ n : ℕ} (h₁ : p₁ ≤ n) (h₂ : p₂ ≤ n) :
    polyBound s k [p₁, p₂] ≤ polyBound s (2 * k) [n] := by sorry
