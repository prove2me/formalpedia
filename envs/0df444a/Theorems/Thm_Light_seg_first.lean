-- Prove2me | Theorems.Thm_Light_seg_first
-- name    : Light.seg_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:53.488016+00:00
-- url     : https://prove2.me/theorems/6ef0f7e8-264f-4014-a3f4-344b0d95deab
-- title:
--   Light: seg first
-- statement:
--   The first of two lists after the size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L81-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L81-L82

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.seg_first (n : ℤ) (l₁ l₂ : List ℤ) : Seg (memOf (n :: (l₁ ++ l₂))) 1 l₁ := by sorry
