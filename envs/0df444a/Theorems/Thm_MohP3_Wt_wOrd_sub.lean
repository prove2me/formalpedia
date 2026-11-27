-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_sub
-- name    : MohP3.Wt.wOrd_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:20.552197+00:00
-- url     : https://prove2.me/theorems/8897b0cb-18e1-5096-ad49-8fd5f1131f43
-- title:
--   Wt: w Ord sub
-- statement:
--   The Wt construction uses the w Ord sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L64-L66
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L64-L66

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

theorem MohP3.Wt.wOrd_sub {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F - G) n := by sorry
