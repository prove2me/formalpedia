-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_X
-- name    : MohP3.Wt.wOrd_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:49.668127+00:00
-- url     : https://prove2.me/theorems/5b2767c1-6164-400e-9f29-754d0a69f73b
-- title:
--   Wt: w Ord X
-- statement:
--   The Wt construction uses the w Ord X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L105-L111
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L105-L111

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

theorem MohP3.Wt.wOrd_X (i : Fin 3) : WOrd (X i : MvPowerSeries (Fin 3) k) (wt (Finsupp.single i 1)) := by sorry
