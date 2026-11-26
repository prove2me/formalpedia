-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_add
-- name    : MohP3.Wt.yOrd_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:03.89536+00:00
-- url     : https://prove2.me/theorems/b0d4077e-ead8-5fc6-a43f-e9f25ac1d9fe
-- title:
--   Wt: y Ord add
-- statement:
--   The Wt construction uses the y Ord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L131-L132
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L131-L132

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

theorem MohP3.Wt.yOrd_add {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p + q) n := by sorry
