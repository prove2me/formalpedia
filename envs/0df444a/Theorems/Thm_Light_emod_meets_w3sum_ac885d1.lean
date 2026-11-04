-- Prove2me | Theorems.Thm_Light_emod_meets_w3sum_ac885d1
-- name    : Light.emod_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:43.135882+00:00
-- url     : https://prove2.me/theorems/1d6b35f6-2f4b-4dd3-beb3-c8ab99aac86c
-- title:
--   Light: emod meets
-- statement:
--   **emod(x, M, fr)** returns the remainder of x modulo M and changes no cell below the free
--   pointer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L236-L264
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L236-L264

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Emod
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}

theorem Light.emod_meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some emodBody) (F : Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    Meets lim P p d [x, Mo, fr] μ (emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ Kept μ μ' fr := by sorry
