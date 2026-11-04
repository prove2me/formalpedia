-- Prove2me | Theorems.Thm_Light_MergeSort_sorted_merge
-- name    : Light.MergeSort.sorted_merge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:23.532041+00:00
-- url     : https://prove2.me/theorems/cc594792-a001-436c-b32c-84a1b038a14f
-- title:
--   Merge Sort: sorted merge
-- statement:
--   The two halves are sorted one after the other, merged into the cells from fr, and copied
--   back.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L115-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L115-L128

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort

theorem Light.MergeSort.sorted_merge {μ μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {a fr h m : ℕ} {L S₁ S₂ : List ℤ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by sorry
