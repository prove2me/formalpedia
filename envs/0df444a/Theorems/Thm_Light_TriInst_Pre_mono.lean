-- Prove2me | Theorems.Thm_Light_TriInst_Pre_mono
-- name    : Light.TriInst.Pre.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:26.77087+00:00
-- url     : https://prove2.me/theorems/d68e8c10-a957-403f-b9ff-f83bcd4f9b48
-- title:
--   Pre: mono
-- statement:
--   The free pointer may grow.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L72-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L72-L77

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Theorems.Thm_Light_ArrayAt_mono
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_ListAt_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono

set_option autoImplicit false
section
open ThreeSumApsp
open Light
open ThreeSumApsp.Spec

theorem Light.TriInst.Pre.mono {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' := by sorry
