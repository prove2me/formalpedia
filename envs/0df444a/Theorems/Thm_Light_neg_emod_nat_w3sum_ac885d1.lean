-- Prove2me | Theorems.Thm_Light_neg_emod_nat_w3sum_ac885d1
-- name    : Light.neg_emod_nat_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:40.385324+00:00
-- url     : https://prove2.me/theorems/ed0a737a-f38c-48b0-ac7c-b9ae2426983c
-- title:
--   Light: neg emod nat
-- statement:
--   The remainder of a negative number.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L98-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L98-L112

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

theorem Light.neg_emod_nat_w3sum_ac885d1 (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by sorry
