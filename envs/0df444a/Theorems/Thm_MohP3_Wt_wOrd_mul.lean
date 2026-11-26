-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_mul
-- name    : MohP3.Wt.wOrd_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:49:58.487444+00:00
-- url     : https://prove2.me/theorems/a2fada51-2864-4190-8c4c-01878abcbef0
-- title:
--   Wt: w Ord mul
-- statement:
--   The Wt construction uses the w Ord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L78-L90
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L78-L90

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

theorem MohP3.Wt.wOrd_mul {F G : MvPowerSeries (Fin 3) k} {m n : ℕ} (hF : WOrd F m) (hG : WOrd G n) :
    WOrd (F * G) (m + n) := by sorry
