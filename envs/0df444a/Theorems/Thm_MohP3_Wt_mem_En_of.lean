-- Prove2me | Theorems.Thm_MohP3_Wt_mem_En_of
-- name    : MohP3.Wt.mem_En_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:51:43.815005+00:00
-- url     : https://prove2.me/theorems/55f84dff-a30f-539d-b484-9dd9e8e166f7
-- title:
--   Wt: mem En of
-- statement:
--   The Wt construction uses the mem En of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L261-L263
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L261-L263

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

theorem MohP3.Wt.mem_En_of {n a b c : ℕ} (h : 6 * a + 8 * b + 10 * c = n) : (a, b, c) ∈ En n := by sorry
