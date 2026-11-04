-- Prove2me | Theorems.Thm_Light_rowByRow_eq
-- name    : Light.rowByRow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:52.865642+00:00
-- url     : https://prove2.me/theorems/985bd6c3-d1ca-479c-9ef1-72ef57fdc5c9
-- title:
--   Light: row By Row eq
-- statement:
--   A square matrix written row by row: the two definitions agree.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L100-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L100-L101

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.rowByRow_eq {n : ℕ} (w : Fin n → Fin n → ℤ) : EndStatement.rowByRow w = rowMajor w := by sorry
