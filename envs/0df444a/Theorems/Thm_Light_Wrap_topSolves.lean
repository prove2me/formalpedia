-- Prove2me | Theorems.Thm_Light_Wrap_topSolves
-- name    : Light.Wrap.topSolves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:53.703613+00:00
-- url     : https://prove2.me/theorems/b8be0604-bee2-4c98-a1ca-f6ff1ea9a1fb
-- title:
--   Wrap: top Solves
-- statement:
--   The compiled program is run within these limits: what the interface to the machine asks for.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L327-L348
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L327-L348

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
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}

theorem Light.Wrap.topSolves (w : Wrap Q task dec) {T : ℕ → ℝ → ℝ} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (hsol : Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, ProgramSolves (ofEnd Q) (P ++ [topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by sorry
