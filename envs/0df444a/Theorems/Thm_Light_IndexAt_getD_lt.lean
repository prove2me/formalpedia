-- Prove2me | Theorems.Thm_Light_IndexAt_getD_lt
-- name    : Light.IndexAt.getD_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:04.442679+00:00
-- url     : https://prove2.me/theorems/74490bc1-aec7-46cf-9ce5-6853a31d31d3
-- title:
--   Index At: get D lt
-- statement:
--   An entry is below `p`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L135-L138

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}

theorem Light.IndexAt.getD_lt (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by sorry
