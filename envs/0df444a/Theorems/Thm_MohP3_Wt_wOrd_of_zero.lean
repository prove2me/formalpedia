-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_of_zero
-- name    : MohP3.Wt.wOrd_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:35.277501+00:00
-- url     : https://prove2.me/theorems/1b66f639-ad4a-4c3a-9ce7-6ac4de21d4f7
-- title:
--   Wt: w Ord of zero
-- statement:
--   The Wt construction uses the w Ord of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L54-L55
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L54-L55

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

theorem MohP3.Wt.wOrd_of_zero {n : ℕ} : WOrd (0 : MvPowerSeries (Fin 3) k) n := by sorry
