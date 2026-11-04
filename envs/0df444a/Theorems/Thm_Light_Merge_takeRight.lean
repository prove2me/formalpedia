-- Prove2me | Theorems.Thm_Light_Merge_takeRight
-- name    : Light.Merge.takeRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:15.063782+00:00
-- url     : https://prove2.me/theorems/e1045c60-d958-478b-8ed4-c3c2919e53d8
-- title:
--   Merge: take Right
-- statement:
--   dst[i + j] := b[j]; j := j + 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L137-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L137-L150

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

theorem Light.Merge.takeRight (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by sorry
