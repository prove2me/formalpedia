-- Prove2me | Theorems.Thm_Light_safe_fourAddresses
-- name    : Light.safe_fourAddresses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:56.506101+00:00
-- url     : https://prove2.me/theorems/60579ff9-2383-462f-90c3-5c5352acb634
-- title:
--   Light: safe four Addresses
-- statement:
--   The arguments n, U and four addresses 1, 1 + n², 1 + 2n², 1 + c n² are safe.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L81-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L81-L94

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

theorem Light.safe_fourAddresses {c : ℕ} (hc : c ≤ 4) {n : ℕ} {lim : Limits} {σ : State}
    (h3 : σ.loc 3 = ((n * n : ℕ) : ℤ)) (hw : ((8 * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k c *' v 3], e.Safe lim σ := by sorry
