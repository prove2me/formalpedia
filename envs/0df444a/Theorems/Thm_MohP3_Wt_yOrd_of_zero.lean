-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_of_zero
-- name    : MohP3.Wt.yOrd_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:41.487821+00:00
-- url     : https://prove2.me/theorems/63647f0b-ed09-55b3-8795-1933cbe97b1a
-- title:
--   Wt: y Ord of zero
-- statement:
--   The Wt construction uses the y Ord of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L129-L129
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L129-L129

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

theorem MohP3.Wt.yOrd_of_zero {n : ℕ} : YOrd (0 : PowerSeries k) n := by sorry
