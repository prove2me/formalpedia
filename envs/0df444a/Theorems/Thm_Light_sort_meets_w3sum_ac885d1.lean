-- Prove2me | Theorems.Thm_Light_sort_meets_w3sum_ac885d1
-- name    : Light.sort_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:29.785184+00:00
-- url     : https://prove2.me/theorems/9a55607f-5908-4f2f-9604-926c6d8d6c96
-- title:
--   Light: sort meets
-- statement:
--   **sort(n, a, fr)** leaves a sorted permutation of the list at a.  Of the cells below fr only the
--   n cells from a may change; the n cells from fr are used.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L201-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L201-L217

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
variable {pSort pHalf pMerge pCopy : ℕ}

theorem Light.sort_meets_w3sum_ac885d1 (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by sorry
