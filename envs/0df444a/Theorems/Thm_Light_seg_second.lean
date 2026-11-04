-- Prove2me | Theorems.Thm_Light_seg_second
-- name    : Light.seg_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:58.600192+00:00
-- url     : https://prove2.me/theorems/c8342aa3-c45c-459d-909a-952d3e7ea0c8
-- title:
--   Light: seg second
-- statement:
--   The second of two lists after the size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L85-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L85-L88

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.seg_second (n : ℤ) (l₁ l₂ : List ℤ) :
    Seg (memOf (n :: (l₁ ++ l₂))) (1 + l₁.length) l₂ := by sorry
