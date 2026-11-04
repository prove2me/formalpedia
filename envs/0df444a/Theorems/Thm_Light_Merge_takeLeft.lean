-- Prove2me | Theorems.Thm_Light_Merge_takeLeft
-- name    : Light.Merge.takeLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:10.176465+00:00
-- url     : https://prove2.me/theorems/c47569ef-b550-492c-8988-0e22bab0cc3b
-- title:
--   Merge: take Left
-- statement:
--   dst[i + j] := a[i]; i := i + 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L121-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L121-L134

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

theorem Light.Merge.takeLeft (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hi : i < l.length)
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by sorry
