-- Prove2me | Theorems.Thm_Light_MergeSort_clog_split_w3sum_ac885d1
-- name    : Light.MergeSort.clog_split_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:24.894953+00:00
-- url     : https://prove2.me/theorems/981394eb-1c28-4d41-9a4a-2c6ce797d322
-- title:
--   Merge Sort: clog split
-- statement:
--   The recursion for n ⌈log₂ n⌉.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L66-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L66-L83

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort

theorem Light.MergeSort.clog_split_w3sum_ac885d1 {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by sorry
