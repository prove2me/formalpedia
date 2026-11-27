-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_pow
-- name    : MohP3.Wt.wOrd_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:34.206368+00:00
-- url     : https://prove2.me/theorems/261e95d0-7940-4712-8af1-2c91e0c7f42c
-- title:
--   Wt: w Ord pow
-- statement:
--   The Wt construction uses the w Ord pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L96-L103
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L96-L103

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

theorem MohP3.Wt.wOrd_pow {F : MvPowerSeries (Fin 3) k} {m : ℕ} (hF : WOrd F m) (e : ℕ) :
    WOrd (F ^ e) (e * m) := by sorry
