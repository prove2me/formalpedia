-- Prove2me | Theorems.Thm_Light_memOf_append_left
-- name    : Light.memOf_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:43.007199+00:00
-- url     : https://prove2.me/theorems/c738ecec-8b89-4008-9d08-536dd2a462e7
-- title:
--   Light: mem Of append left
-- statement:
--   A cell in the first part of a concatenation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L63-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L63-L66

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.memOf_append_left {l₁ : List ℤ} (l₂ : List ℤ) {a : ℕ} (h : a < l₁.length) :
    memOf (l₁ ++ l₂) a = memOf l₁ a := by sorry
