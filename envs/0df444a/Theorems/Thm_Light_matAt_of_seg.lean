-- Prove2me | Theorems.Thm_Light_matAt_of_seg
-- name    : Light.matAt_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:53.765323+00:00
-- url     : https://prove2.me/theorems/797dde2a-ef22-4306-807b-3d32fbaee0df
-- title:
--   Light: mat At of seg
-- statement:
--   A matrix written row by row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L91-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RowMajor.lean#L91-L97

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam

theorem Light.matAt_of_seg {n k : ℕ} {μ : ℕ → ℤ} {a : ℕ} {A : Matrix (Fin n) (Fin k) ℤ}
    (h : Seg μ a (rowMajor A)) : MatAt μ a A := by sorry
