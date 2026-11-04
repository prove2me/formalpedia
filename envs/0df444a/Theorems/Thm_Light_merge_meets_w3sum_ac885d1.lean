-- Prove2me | Theorems.Thm_Light_merge_meets_w3sum_ac885d1
-- name    : Light.merge_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:23.591516+00:00
-- url     : https://prove2.me/theorems/5a5abf33-87d1-421f-ac13-0f6a47c7372d
-- title:
--   Light: merge meets
-- statement:
--   **merge(a, na, b, nb, dst)** writes `List.merge` of the two lists to dst and changes nothing
--   else.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L157-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L157-L194

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

theorem Light.merge_meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some mergeBody)
    (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) := by sorry
