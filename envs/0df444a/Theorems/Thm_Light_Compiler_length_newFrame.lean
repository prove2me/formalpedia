-- Prove2me | Theorems.Thm_Light_Compiler_length_newFrame
-- name    : Light.Compiler.length_newFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:16.533938+00:00
-- url     : https://prove2.me/theorems/bfd8e44f-3c01-4da6-b50f-0e181fa4100e
-- title:
--   Compiler: length new Frame
-- statement:
--   The code between the arguments and the jump has 2 F + 4 instructions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L259-L260
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L259-L260

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.length_newFrame (F n ret : ℕ) : (newFrame F n ret).length = 2 * F + 4 := by sorry
