-- Prove2me | Theorems.Thm_MohP3_Wt_wt_dd
-- name    : MohP3.Wt.wt_dd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:44.277907+00:00
-- url     : https://prove2.me/theorems/2150dfef-7af9-4145-9dc8-a943cae8cdc0
-- title:
--   Wt: wt dd
-- statement:
--   The Wt construction uses the wt dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L231-L232
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L231-L232

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

theorem MohP3.Wt.wt_dd (a b c : ℕ) : wt (dd a b c) = 6 * a + 8 * b + 10 * c := by sorry
