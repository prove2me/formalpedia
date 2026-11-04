-- Prove2me | Theorems.Thm_Light_Merge_step_left_end
-- name    : Light.Merge.step_left_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:40.280211+00:00
-- url     : https://prove2.me/theorems/aa1d0504-e396-43d0-9d7f-c5737def0f54
-- title:
--   Merge: step left end
-- statement:
--   The Merge construction uses the step left end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L43-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L43-L45

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {l r : List ℤ} {i j : ℕ}

theorem Light.Merge.step_left_end (hi : i < l.length) (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by sorry
