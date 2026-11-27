-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_sum
-- name    : MohP3.Wt.yOrd_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:58.158814+00:00
-- url     : https://prove2.me/theorems/43c57037-c1b5-5d93-ab31-02b6a9ed123e
-- title:
--   Wt: y Ord sum
-- statement:
--   The Wt construction uses the y Ord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L140-L148
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L140-L148

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

theorem MohP3.Wt.yOrd_sum {ι : Type*} {s : Finset ι} {p : ι → PowerSeries k} {n : ℕ}
    (h : ∀ i ∈ s, YOrd (p i) n) : YOrd (∑ i ∈ s, p i) n := by sorry
