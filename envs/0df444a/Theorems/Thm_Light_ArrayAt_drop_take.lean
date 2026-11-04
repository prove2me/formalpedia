-- Prove2me | Theorems.Thm_Light_ArrayAt_drop_take
-- name    : Light.ArrayAt.drop_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:06.101633+00:00
-- url     : https://prove2.me/theorems/401677de-d7c6-4035-ae0e-8b2b0f7c1985
-- title:
--   Array At: drop take
-- statement:
--   The `n` entries from place `k` on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L100-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L100-L103

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_drop_take

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.drop_take (h : ArrayAt μ a l N U top) (hk : k + n ≤ N) :
    ArrayAt μ (a + k) ((l.drop k).take n) n U top := by sorry
