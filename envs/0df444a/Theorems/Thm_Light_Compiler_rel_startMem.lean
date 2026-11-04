-- Prove2me | Theorems.Thm_Light_Compiler_rel_startMem
-- name    : Light.Compiler.rel_startMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:57.183551+00:00
-- url     : https://prove2.me/theorems/90a8a0aa-2bf5-4fe8-8c2d-db6e2c979477
-- title:
--   Compiler: rel start Mem
-- statement:
--   After the start-up code the memory represents the state in which the outermost statement
--   starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
--   the cells below -2 of the initial memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L196-L223
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L196-L223

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.rel_startMem (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) := by sorry
