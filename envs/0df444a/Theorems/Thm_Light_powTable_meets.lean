-- Prove2me | Theorems.Thm_Light_powTable_meets
-- name    : Light.powTable_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:36.772842+00:00
-- url     : https://prove2.me/theorems/f486be79-7b73-47b0-ac8e-4804acfcb5f0
-- title:
--   Light: pow Table meets
-- statement:
--   **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
--   nothing else.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L107-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L107-L113

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Int.SuccPred
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open PowTable

theorem Light.powTable_meets {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L := by sorry
