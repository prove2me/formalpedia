-- Prove2me | Theorems.Thm_Light_ArrayAt_abs_read_le
-- name    : Light.ArrayAt.abs_read_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:57.415186+00:00
-- url     : https://prove2.me/theorems/983d20ae-6800-4219-8993-cbb9ddc141a3
-- title:
--   Array At: abs read le
-- statement:
--   A cell of an array holds a number of absolute value at most `U`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L95-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L95-L97

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.abs_read_le (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by sorry
