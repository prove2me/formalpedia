-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_eq_zero
-- name    : MohP3.Wt.wOrd_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:59:48.04927+00:00
-- url     : https://prove2.me/theorems/51b2592a-5eab-51b8-8c7f-feea57d76769
-- title:
--   Wt: w Ord eq zero
-- statement:
--   The Wt construction uses the w Ord eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L113-L115
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L113-L115

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

theorem MohP3.Wt.wOrd_eq_zero {F : MvPowerSeries (Fin 3) k} (h : ∀ n, WOrd F n) : F = 0 := by sorry
