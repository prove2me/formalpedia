-- Prove2me | Theorems.Thm_Light_seg_memOf
-- name    : Light.seg_memOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:48.524454+00:00
-- url     : https://prove2.me/theorems/81c350f0-dd89-423e-9863-9dce2ab66dc7
-- title:
--   Light: seg mem Of
-- statement:
--   A part of a concatenation is a segment of the memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L75-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L75-L78

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.seg_memOf (l₁ l l₂ : List ℤ) : Seg (memOf (l₁ ++ l ++ l₂)) l₁.length l := by sorry
