-- Prove2me | Theorems.Thm_Light_triPre_of_arrays
-- name    : Light.triPre_of_arrays
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:40.019248+00:00
-- url     : https://prove2.me/theorems/a7d099c4-2d09-43e9-95dc-2c16868e6112
-- title:
--   Light: tri Pre of arrays
-- statement:
--   Three matrices one after the other, with the free pointer behind them, are an instance.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L80-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L80-L87

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
set_option autoImplicit false
section
open ThreeSumApsp
open Light
open ThreeSumApsp.Spec

theorem Light.triPre_of_arrays {n U base : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n))) :
    (⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩ : TriInst).Pre μ
      (base + 3 * (n * n)) := by sorry
