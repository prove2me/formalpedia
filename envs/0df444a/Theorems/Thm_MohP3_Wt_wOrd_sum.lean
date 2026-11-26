-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_sum
-- name    : MohP3.Wt.wOrd_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:32.756737+00:00
-- url     : https://prove2.me/theorems/c1dfe6cf-17fb-5a3c-9b70-702ad793037e
-- title:
--   Wt: w Ord sum
-- statement:
--   The Wt construction uses the w Ord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L68-L76
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L68-L76

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

theorem MohP3.Wt.wOrd_sum {ι : Type*} {s : Finset ι} {F : ι → MvPowerSeries (Fin 3) k} {n : ℕ}
    (h : ∀ i ∈ s, WOrd (F i) n) : WOrd (∑ i ∈ s, F i) n := by sorry
