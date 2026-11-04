-- Prove2me | Theorems.Thm_Light_sqrt_meets_w3sum_ac885d1
-- name    : Light.sqrt_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:25.23059+00:00
-- url     : https://prove2.me/theorems/1d7653d1-b3b9-4daf-955f-cc05bdeb74c1
-- title:
--   Light: sqrt meets
-- statement:
--   **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean#L48-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean#L48-L77

import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.sqrt_meets_w3sum_ac885d1 {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by sorry
