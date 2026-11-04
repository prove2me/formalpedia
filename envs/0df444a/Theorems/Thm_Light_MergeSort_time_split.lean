-- Prove2me | Theorems.Thm_Light_MergeSort_time_split
-- name    : Light.MergeSort.time_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:25.208719+00:00
-- url     : https://prove2.me/theorems/18df5fa5-4284-4efb-a1fd-da57b28f68be
-- title:
--   Merge Sort: time split
-- statement:
--   The recursion for the number of steps.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L93-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L93-L97

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort

theorem Light.MergeSort.time_split {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by sorry
