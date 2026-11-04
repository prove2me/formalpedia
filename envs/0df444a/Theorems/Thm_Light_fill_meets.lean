-- Prove2me | Theorems.Thm_Light_fill_meets
-- name    : Light.fill_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:37.580057+00:00
-- url     : https://prove2.me/theorems/49a0d47c-05eb-41f5-a2e9-c3c8e056b1b8
-- title:
--   Light: fill meets
-- statement:
--   **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Copy.lean#L84-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Copy.lean#L84-L90

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n := by sorry
