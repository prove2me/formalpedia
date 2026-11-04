-- Prove2me | Theorems.Thm_Light_Seg_of_kept
-- name    : Light.Seg.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:08:03.571042+00:00
-- url     : https://prove2.me/theorems/1d2cfd4b-4cae-4c19-b5fb-4eeca45334e0
-- title:
--   Seg: of kept
-- statement:
--   A list below fr stays where it is if nothing below fr changes.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L75-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L75-L77

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : Seg μ a l) (hk : Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : Seg μ' a l := by sorry
