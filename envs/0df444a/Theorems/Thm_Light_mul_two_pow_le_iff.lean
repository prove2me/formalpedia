-- Prove2me | Theorems.Thm_Light_mul_two_pow_le_iff
-- name    : Light.mul_two_pow_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:38.603988+00:00
-- url     : https://prove2.me/theorems/85955129-d4b9-4ccc-b2df-fb001b680a9b
-- title:
--   Light: mul two pow le iff
-- statement:
--   The multiple M 2^i is at most a exactly for i below the number of doublings.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L87-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L87-L88

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

theorem Light.mul_two_pow_le_iff {a M i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < emodRounds a M := by sorry
