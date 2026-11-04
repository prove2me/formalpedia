-- Prove2me | Theorems.Thm_Light_memOf_append_right
-- name    : Light.memOf_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:43.563148+00:00
-- url     : https://prove2.me/theorems/0158949a-8bc3-4256-8ed1-4f7fa989c718
-- title:
--   Light: mem Of append right
-- statement:
--   A cell after the first part of a concatenation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L69-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L69-L72

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.memOf_append_right (l₁ l₂ : List ℤ) (a : ℕ) :
    memOf (l₁ ++ l₂) (l₁.length + a) = memOf l₂ a := by sorry
