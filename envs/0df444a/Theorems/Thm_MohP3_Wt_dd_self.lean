-- Prove2me | Theorems.Thm_MohP3_Wt_dd_self
-- name    : MohP3.Wt.dd_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:51:28.976241+00:00
-- url     : https://prove2.me/theorems/db14607d-44aa-4dc5-87fb-4314d325ae50
-- title:
--   Wt: dd self
-- statement:
--   The Wt construction uses the dd self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L234-L236
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L234-L236

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

theorem MohP3.Wt.dd_self (d : Fin 3 →₀ ℕ) : dd (d 0) (d 1) (d 2) = d := by sorry
