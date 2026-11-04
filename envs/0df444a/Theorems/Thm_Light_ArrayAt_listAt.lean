-- Prove2me | Theorems.Thm_Light_ArrayAt_listAt
-- name    : Light.ArrayAt.listAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:39.128871+00:00
-- url     : https://prove2.me/theorems/f42f659c-1f1c-46b8-8fb8-65a16bd2a63d
-- title:
--   Array At: list At
-- statement:
--   An array without the bound on its entries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L78-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L78-L78

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := by sorry
