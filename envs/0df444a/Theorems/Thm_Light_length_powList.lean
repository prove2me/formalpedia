-- Prove2me | Theorems.Thm_Light_length_powList
-- name    : Light.length_powList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:55.332412+00:00
-- url     : https://prove2.me/theorems/1a92a3eb-cf43-4a33-9914-bfc14a535094
-- title:
--   Light: length pow List
-- statement:
--   The Light construction uses the length pow List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L28-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L28-L28

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Int.SuccPred
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.length_powList (b L : ℕ) : (powList b L).length = L := by sorry
