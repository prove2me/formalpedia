-- Prove2me | Theorems.Thm_Light_ArrayAt_read
-- name    : Light.ArrayAt.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:41.245309+00:00
-- url     : https://prove2.me/theorems/e99e38f0-eb9a-481e-8d06-74f2f6f543c3
-- title:
--   Array At: read
-- statement:
--   Reading a cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L92-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L92-L92

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := by sorry
