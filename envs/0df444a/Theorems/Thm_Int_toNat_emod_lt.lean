-- Prove2me | Theorems.Thm_Int_toNat_emod_lt
-- name    : Int.toNat_emod_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:56.462301+00:00
-- url     : https://prove2.me/theorems/cbcd6312-3768-4945-9ef5-e914e2ca9d9f
-- title:
--   Int: to Nat emod lt
-- statement:
--   The residue of an integer modulo `M ≥ 1`, as a natural number, is below `M`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L108-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L108-L110

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Int

theorem Int.toNat_emod_lt {M : ℕ} (hM : 0 < M) (x : ℤ) : (x % (M : ℤ)).toNat < M := by sorry
