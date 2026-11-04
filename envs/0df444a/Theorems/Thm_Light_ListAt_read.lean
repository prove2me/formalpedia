-- Prove2me | Theorems.Thm_Light_ListAt_read
-- name    : Light.ListAt.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:11.863774+00:00
-- url     : https://prove2.me/theorems/fc236824-b6bc-4efe-bef9-282146396a66
-- title:
--   List At: read
-- statement:
--   Reading a cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L63-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L63-L64

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ListAt

theorem Light.ListAt.read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 := by sorry
