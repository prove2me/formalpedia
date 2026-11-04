-- Prove2me | Theorems.Thm_Light_ListAt_drop_take
-- name    : Light.ListAt.drop_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:44.066229+00:00
-- url     : https://prove2.me/theorems/489059ad-5531-4278-b225-0f3a8d3aec47
-- title:
--   List At: drop take
-- statement:
--   The `n` entries from place `k` on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L67-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L67-L71

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_drop_take

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ListAt

theorem Light.ListAt.drop_take (h : ListAt μ a l N top) (hk : k + n ≤ N) :
    ListAt μ (a + k) ((l.drop k).take n) n top := by sorry
