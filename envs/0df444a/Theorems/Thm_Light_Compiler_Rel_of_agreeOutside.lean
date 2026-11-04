-- Prove2me | Theorems.Thm_Light_Compiler_Rel_of_agreeOutside
-- name    : Light.Compiler.Rel.of_agreeOutside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:07:57.588495+00:00
-- url     : https://prove2.me/theorems/23f29cce-d91e-44e8-adc9-16ca5b8aed88
-- title:
--   Rel: of agree Outside
-- statement:
--   After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
--   as soon as FP, the local variables and the memory cells are right.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L230-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L230-L242

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.of_agreeOutside {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m')
    (hs : s ⊆ (Constants Z.disp)ᶜ) (hfp : m' cFP = wd W (cStack q'))
    (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' := by sorry
