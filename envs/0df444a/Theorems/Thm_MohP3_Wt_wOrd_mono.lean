-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_mono
-- name    : MohP3.Wt.wOrd_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:56.873036+00:00
-- url     : https://prove2.me/theorems/45e82571-19f4-40fc-8ccb-a10aafb32e65
-- title:
--   Wt: w Ord mono
-- statement:
--   The Wt construction uses the w Ord mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L51-L52
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L51-L52

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

theorem MohP3.Wt.wOrd_mono {F : MvPowerSeries (Fin 3) k} {m n : ℕ} (h : n ≤ m) (hF : WOrd F m) :
    WOrd F n := by sorry
