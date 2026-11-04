-- Prove2me | Theorems.Thm_Light_Emod_table_ends_w3sum_ac885d1
-- name    : Light.Emod.table_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:41.655745+00:00
-- url     : https://prove2.me/theorems/b177d243-5dec-43da-91e7-7d856c39fffd
-- title:
--   Emod: table ends
-- statement:
--   **The table.**  With K doublings, the K multiples M 2^j ≤ a are written.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L130-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L130-L165

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

theorem Light.Emod.table_ends_w3sum_ac885d1 (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Ends lim P d emodTable ⟨frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨frame [x, Mo, fr, a, emodRounds a Mo, ((Mo * 2 ^ emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        Table μ μ' Mo fr (emodRounds a Mo) := by sorry
