-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_zero
-- name    : MohP3.Wt.wOrd_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:32.795937+00:00
-- url     : https://prove2.me/theorems/e5d4ba2a-0de9-4dda-8760-1a46e6050107
-- title:
--   Wt: w Ord zero
-- statement:
--   The Wt construction uses the w Ord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L48-L49
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L48-L49

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

theorem MohP3.Wt.wOrd_zero (F : MvPowerSeries (Fin 3) k) : WOrd F 0 := by sorry
