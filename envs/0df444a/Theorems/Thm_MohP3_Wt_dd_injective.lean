-- Prove2me | Theorems.Thm_MohP3_Wt_dd_injective
-- name    : MohP3.Wt.dd_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:51:36.016732+00:00
-- url     : https://prove2.me/theorems/0dc87e57-c812-433b-bf0c-c45e907370a3
-- title:
--   Wt: dd injective
-- statement:
--   The Wt construction uses the dd injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L238-L243
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L238-L243

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

theorem MohP3.Wt.dd_injective {a b c a' b' c' : ℕ} (h : dd a b c = dd a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by sorry
