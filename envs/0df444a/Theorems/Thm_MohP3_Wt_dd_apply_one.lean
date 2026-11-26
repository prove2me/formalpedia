-- Prove2me | Theorems.Thm_MohP3_Wt_dd_apply_one
-- name    : MohP3.Wt.dd_apply_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:41.637801+00:00
-- url     : https://prove2.me/theorems/935bd033-91b4-5f17-b610-0ae819f0fb0c
-- title:
--   Wt: dd apply one
-- statement:
--   The Wt construction uses the dd apply one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L225-L226
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L225-L226

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

theorem MohP3.Wt.dd_apply_one (a b c : ℕ) : dd a b c 1 = b := by sorry
