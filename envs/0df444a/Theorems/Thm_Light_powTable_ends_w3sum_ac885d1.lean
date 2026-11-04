-- Prove2me | Theorems.Thm_Light_powTable_ends_w3sum_ac885d1
-- name    : Light.powTable_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:59.633452+00:00
-- url     : https://prove2.me/theorems/f35bc378-e836-4e9d-9d45-1693d6aba82f
-- title:
--   Light: pow Table ends
-- statement:
--   The body of powTable writes the powers of b and changes nothing else, whatever its local
--   variables hold apart from the three arguments.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L70-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L70-L103

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

theorem Light.powTable_ends_w3sum_ac885d1 {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by sorry
