-- Prove2me | Theorems.Thm_Light_Compiler_temps_subset_scratch
-- name    : Light.Compiler.temps_subset_scratch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:08:56.419364+00:00
-- url     : https://prove2.me/theorems/70f725ff-a2ce-4669-ae66-92e1bccaf2fc
-- title:
--   Compiler: temps subset scratch
-- statement:
--   What an expression may change is scratch.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L162-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L162-L162

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.temps_subset_scratch {k : ℕ} : Temps k F ⊆ Scratch F := by sorry
