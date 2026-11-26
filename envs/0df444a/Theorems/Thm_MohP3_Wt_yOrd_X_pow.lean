-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_X_pow
-- name    : MohP3.Wt.yOrd_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:51:27.045798+00:00
-- url     : https://prove2.me/theorems/e5e47a72-63cb-4d2e-bd4d-2cc71f769a07
-- title:
--   Wt: y Ord X pow
-- statement:
--   The Wt construction uses the y Ord X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L166-L170
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L166-L170

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

theorem MohP3.Wt.yOrd_X_pow (e : ℕ) : YOrd ((PowerSeries.X : PowerSeries k) ^ e) (8 * e) := by sorry
