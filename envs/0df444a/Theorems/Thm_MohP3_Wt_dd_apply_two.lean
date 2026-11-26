-- Prove2me | Theorems.Thm_MohP3_Wt_dd_apply_two
-- name    : MohP3.Wt.dd_apply_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:39.977864+00:00
-- url     : https://prove2.me/theorems/e0d224ef-abc3-5d4c-a08f-74f51aa6b59c
-- title:
--   Wt: dd apply two
-- statement:
--   The Wt construction uses the dd apply two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L228-L229
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L228-L229

module
public import Mathlib
public import Definitions.Def_MohP3_Order
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]

theorem MohP3.Wt.dd_apply_two (a b c : ℕ) : dd a b c 2 = c := by sorry
