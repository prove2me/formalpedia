-- Prove2me | Theorems.Thm_MohP3_Wt_wOrd_sub_top_part
-- name    : MohP3.Wt.wOrd_sub_top_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:33.255037+00:00
-- url     : https://prove2.me/theorems/9f908914-6685-5729-92de-59808bb0eabe
-- title:
--   Wt: w Ord sub top part
-- statement:
--   Splitting off the weight-`n` homogeneous part of a series of weighted order `≥ n`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L266-L301
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L266-L301

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

theorem MohP3.Wt.wOrd_sub_top_part (F : MvPowerSeries (Fin 3) k) (n : ℕ) (hF : WOrd F n) :
    WOrd (F - ∑ p ∈ En n, MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2)
      (coeff (dd p.1 p.2.1 p.2.2) F)) (n + 1) := by sorry
