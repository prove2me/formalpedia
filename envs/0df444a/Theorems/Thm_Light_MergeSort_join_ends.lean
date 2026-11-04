-- Prove2me | Theorems.Thm_Light_MergeSort_join_ends
-- name    : Light.MergeSort.join_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:22.929688+00:00
-- url     : https://prove2.me/theorems/4f4d6a2a-4a84-41ac-be02-ec227aa79424
-- title:
--   Merge Sort: join ends
-- statement:
--   Two lists, one after the other in the memory, are merged into the cells from fr and copied
--   back.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L134-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L134-L150

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

theorem Light.MergeSort.join_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) {d a fr h n : ℕ} {r : ℤ} {S₁ S₂ : List ℤ} {μ : ℕ → ℤ}
    (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n) (hS₁ : Seg μ a S₁)
    (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧
        SameOutside μ' σ'.mem a n := by sorry
