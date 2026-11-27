-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_neg
-- name    : MohP3.Wt.yOrd_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:51:22.384327+00:00
-- url     : https://prove2.me/theorems/2df98b53-7dde-5656-b370-922d4194b018
-- title:
--   Wt: y Ord neg
-- statement:
--   The Wt construction uses the y Ord neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L134-L135
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L134-L135

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

theorem MohP3.Wt.yOrd_neg {p : PowerSeries k} {n : ℕ} (hp : YOrd p n) : YOrd (-p) n := by sorry
