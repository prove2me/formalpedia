-- Prove2me | Theorems.Thm_Light_Merge_step_right
-- name    : Light.Merge.step_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:38.391855+00:00
-- url     : https://prove2.me/theorems/3dc73452-06fe-4fec-9583-d33de9515b45
-- title:
--   Merge: step right
-- statement:
--   The Merge construction uses the step right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L38-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L38-L41

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {l r : List ℤ} {i j : ℕ}

theorem Light.Merge.step_right (hi : i < l.length) (hj : j < r.length) (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by sorry
