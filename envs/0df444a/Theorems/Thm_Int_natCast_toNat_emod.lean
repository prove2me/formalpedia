-- Prove2me | Theorems.Thm_Int_natCast_toNat_emod
-- name    : Int.natCast_toNat_emod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:56.998472+00:00
-- url     : https://prove2.me/theorems/40a9147d-0b6a-4bda-8850-f82847363816
-- title:
--   Int: nat Cast to Nat emod
-- statement:
--   The residue of an integer modulo `M ≥ 1` is a natural number.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L113-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L113-L114

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Int

theorem Int.natCast_toNat_emod {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) := by sorry
