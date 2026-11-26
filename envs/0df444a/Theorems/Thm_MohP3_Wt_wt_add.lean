-- Prove2me | Theorems.Thm_MohP3_Wt_wt_add
-- name    : MohP3.Wt.wt_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:50:22.603715+00:00
-- url     : https://prove2.me/theorems/5ddbdb9e-f060-434b-88e8-824c30e28c55
-- title:
--   Wt: wt add
-- statement:
--   The Wt construction uses the wt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L39-L40
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L39-L40

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

theorem MohP3.Wt.wt_add (d e : Fin 3 →₀ ℕ) : wt (d + e) = wt d + wt e := by sorry
