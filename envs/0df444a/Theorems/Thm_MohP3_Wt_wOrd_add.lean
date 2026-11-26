-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_add
-- name    : MohP3.Wt.wOrd_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:49.262356+00:00
-- url     : https://prove2.me/theorems/8d6a8343-b6e3-50e5-bc52-013eecaf43e5
-- title:
--   Wt: w Ord add
-- statement:
--   The Wt construction uses the w Ord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L57-L59
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L57-L59

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

theorem MohP3.Wt.wOrd_add {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F + G) n := by sorry
