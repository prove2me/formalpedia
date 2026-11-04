-- Prove2me | Theorems.Thm_Light_getD_rowMajor
-- name    : Light.getD_rowMajor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:47.529181+00:00
-- url     : https://prove2.me/theorems/6624107a-7da4-4264-a8e0-4eef9d5b2bb0
-- title:
--   Light: get D row Major
-- statement:
--   The entry `(i, j)` of an `n × m` matrix is at place `i m + j`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L35-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L35-L49

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.getD_rowMajor : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m),
    (rowMajor A).getD ((i : ℕ) * m + (j : ℕ)) 0 = A i j
  := by sorry
