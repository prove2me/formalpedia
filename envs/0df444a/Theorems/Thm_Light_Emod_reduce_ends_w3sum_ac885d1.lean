-- Prove2me | Theorems.Thm_Light_Emod_reduce_ends_w3sum_ac885d1
-- name    : Light.Emod.reduce_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:42.289017+00:00
-- url     : https://prove2.me/theorems/4d9c8aef-34fe-47c8-8a01-111c7b28027a
-- title:
--   Emod: reduce ends
-- statement:
--   **The subtractions.**  What is left of a after the multiples M 2^j have been subtracted, from
--   the largest down, where possible, is the remainder of a.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L169-L211
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L169-L211

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

theorem Light.Emod.reduce_ends_w3sum_ac885d1 (F : Pre lim Mo V fr) (haV : a ≤ V) {μ' : ℕ → ℤ} {t : ℤ}
    (tab : Table μ μ' Mo fr (emodRounds a Mo)) :
    Ends lim P d emodReduce ⟨frame [x, Mo, fr, a, emodRounds a Mo, t], μ'⟩
      (24 * emodRounds a Mo + 4) fun σ' => σ' = ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ := by sorry
