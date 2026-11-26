-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_zero
-- name    : MohP3.Wt.yOrd_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:44.523193+00:00
-- url     : https://prove2.me/theorems/ba2991c1-1468-45ff-8f77-fa96b7f1781f
-- title:
--   Wt: y Ord zero
-- statement:
--   The Wt construction uses the y Ord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L123-L124
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L123-L124

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

theorem MohP3.Wt.yOrd_zero (p : PowerSeries k) : YOrd p 0 := by sorry
