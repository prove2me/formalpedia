-- Prove2me | Theorems.Thm_Light_getElem_powList
-- name    : Light.getElem_powList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:33.957761+00:00
-- url     : https://prove2.me/theorems/128f13d8-63e7-4873-a011-345039e17da7
-- title:
--   Light: get Elem pow List
-- statement:
--   The Light construction uses the get Elem pow List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L30-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L30-L32

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Int.SuccPred
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by sorry
