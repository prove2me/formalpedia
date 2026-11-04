-- Prove2me | Theorems.Thm_Light_IndexAt_read
-- name    : Light.IndexAt.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:05.387207+00:00
-- url     : https://prove2.me/theorems/d8c8696f-6ac7-47de-97d9-c11de4a84789
-- title:
--   Index At: read
-- statement:
--   Reading a cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L131-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L131-L132

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}

theorem Light.IndexAt.read (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) := by sorry
