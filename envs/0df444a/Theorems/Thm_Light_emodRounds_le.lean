-- Prove2me | Theorems.Thm_Light_emodRounds_le
-- name    : Light.emodRounds_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:38.316959+00:00
-- url     : https://prove2.me/theorems/f8e678e8-feb5-4481-8505-49516f5d1ff7
-- title:
--   Light: emod Rounds le
-- statement:
--   There are at most log₂ (V + 1) + 1 doublings for a number up to V.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L91-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L91-L95

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

theorem Light.emodRounds_le {a M V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by sorry
