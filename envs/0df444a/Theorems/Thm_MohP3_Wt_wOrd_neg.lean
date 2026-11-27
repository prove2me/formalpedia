-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_neg
-- name    : MohP3.Wt.wOrd_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:41.29614+00:00
-- url     : https://prove2.me/theorems/739e33f4-d81a-42ab-bfe2-0e67b06b0cde
-- title:
--   Wt: w Ord neg
-- statement:
--   The Wt construction uses the w Ord neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L61-L62
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L61-L62

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

theorem MohP3.Wt.wOrd_neg {F : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) : WOrd (-F) n := by sorry
