-- Prove2me | Theorems.Thm_Light_mem_rowMajor_self
-- name    : Light.mem_rowMajor_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:43.667125+00:00
-- url     : https://prove2.me/theorems/fee2e99c-6dde-42b2-ba93-8537c945befa
-- title:
--   Light: mem row Major self
-- statement:
--   Every entry of a matrix stands in the list of its rows.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L57-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L57-L60

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.mem_rowMajor_self {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m) :
    A i j ∈ rowMajor A := by sorry
