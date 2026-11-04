-- Prove2me | Theorems.Thm_Light_copy_meets
-- name    : Light.copy_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:37.3472+00:00
-- url     : https://prove2.me/theorems/d11e70f0-afa2-428d-b6e2-d5ef5aae379c
-- title:
--   Light: copy meets
-- statement:
--   **copy(src, dst, n)** copies the n cells from src to dst and changes nothing else.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Copy.lean#L46-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Copy.lean#L46-L62

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by sorry
