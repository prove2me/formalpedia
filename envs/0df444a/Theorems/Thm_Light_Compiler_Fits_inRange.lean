-- Prove2me | Theorems.Thm_Light_Compiler_Fits_inRange
-- name    : Light.Compiler.Fits.inRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:15.314199+00:00
-- url     : https://prove2.me/theorems/e6ead069-db14-4837-8bdf-393a81e86829
-- title:
--   Fits: in Range
-- statement:
--   A number within the limit on words is in the range of words.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L66-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L66-L68

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.Fits.inRange {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v := by sorry
