-- Prove2me | Theorems.Thm_Light_pow_spec
-- name    : Light.pow_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:49.802675+00:00
-- url     : https://prove2.me/theorems/ab73ec2d-7fae-4df7-acf5-2ce8ef130655
-- title:
--   Light: pow spec
-- statement:
--   The loop that is written out κ times turns U = 1 into U = n^κ.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L60-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L60-L78

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.pow_spec {n : ℕ} (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) : ∀ κ : ℕ, ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
    Ends lim P d (powStmt κ) ⟨frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  := by sorry
