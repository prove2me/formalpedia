-- Prove2me | Theorems.Thm_Light_Need_Ok_mono
-- name    : Light.Need.Ok.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:49.911465+00:00
-- url     : https://prove2.me/theorems/11cfb915-f782-49be-9225-4e89aef28c86
-- title:
--   Ok: mono
-- statement:
--   A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
--   larger depth if the sums are not larger.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L60-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Tasks.lean#L60-L63

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono

set_option autoImplicit false
section
open Light
open ThreeSumApsp

theorem Light.Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' := by sorry
